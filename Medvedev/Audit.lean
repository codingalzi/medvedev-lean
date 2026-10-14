import Medvedev
import Lean.Util.CollectAxioms
import Lean.Replay

/-!
# 감사 진입점 (단순화 버전)

1. 공리 감사: 모든 프로젝트 선언이 의존하는 공리를 Mathlib까지 추적하여
   `propext`, `Classical.choice`, `Quot.sound` 외에는 없음을 확인한다.
   (`sorry`는 `sorryAx`, `native_decide`는 `Lean.ofReduceBool` 공리로 나타나므로 여기서 걸린다.)
2. 커널 재검사: 프로젝트 이외의 모듈(Lean 코어, Mathlib 등)만 불러온 새 환경에
   Lean 코어의 `Environment.replay`로 프로젝트 선언을 모두 다시 넣어 커널이 검사하게 한다.
   생성자와 재귀자는 귀납 타입을 다시 받을 때 커널이 새로 만든 것과 저장된 것이
   같은지 `replay`가 비교한다.

외부 라이브러리 선언은 신뢰하는 전제로 둔다.
감사 함수는 이 파일을 끝까지 컴파일한 뒤 별도 파일에서 import하여 실행한다
(`scripts/run_audit.py`). 그래야 이 파일의 어느 위치에 추가된 선언도 감사 대상에 포함된다.
-/

#print axioms Medvedev.WangCode.correct
#print axioms Medvedev.tiling_iff_not_valid
#print axioms Medvedev.recognition
#print axioms Medvedev.Formula.pi01_characterization
#print axioms Medvedev.nonhalting_reduction
#print axioms Medvedev.Domino.MachineCode.domino_correct
#print axioms Medvedev.Domino.MachineCode.nonhalting_iff_valid
#print axioms Medvedev.Domino.ArithmeticBackground.no_torus
#print axioms Medvedev.Domino.windowHalts_iff_halts
#print axioms Medvedev.Domino.MachineCode.halts_iff_colored_periodic
#print axioms Medvedev.Domino.MachineCode.absolute_domino_correct
#print axioms Medvedev.Domino.Machine.halts_iff_absoluteHalts
#print axioms Medvedev.Domino.StandardTM.halts_iff
#print axioms Medvedev.Domino.StandardTM.nonhalting_iff_valid
#print axioms Medvedev.Domino.TM0Problem.compiler_correct
#print axioms Medvedev.rePred_not_inML
#print axioms Medvedev.not_computablePred_inML
#print axioms Medvedev.not_rePred_inML
#print axioms Medvedev.no_computable_bound

open Lean in
set_option maxHeartbeats 0 in
def Medvedev.auditProject : Elab.Command.CommandElabM Unit := do
  let env ← getEnv

  -- 감사 범위. 최상위 소스 파일이 Medvedev.lean 하나뿐이면 (나머지는 모두 Medvedev/ 아래),
  -- 프로젝트 모듈은 정확히 이름이 `Medvedev`로 시작하는 모듈들이다.
  let root : System.FilePath := (← IO.getEnv "MEDVEDEV_AUDIT_ROOT").getD "."
  let topLevel := (← root.readDir).filter (·.path.extension == some "lean") |>.map (·.fileName)
  unless topLevel == #["Medvedev.lean"] do
    throwError "Unexpected top-level Lean files in {root}: {topLevel}"
  let isProjectModule (m : Name) : Bool := (`Medvedev).isPrefixOf m
  let isProject (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => isProjectModule env.header.moduleNames[idx.toNat]!
    | none => true -- 현재 파일에서 정의된 선언

  -- 프로젝트 선언 수집. unsafe 선언은 커널 검사를 받지 않으므로 금지한다.
  let mut project : Std.HashMap Name ConstantInfo := {}
  for (n, ci) in env.constants.toList do
    if isProject n then
      if ci.isUnsafe then throwError "Unsafe project declaration is forbidden: {n}"
      project := project.insert n ci
  if project.isEmpty then throwError "No project declarations were audited"

  -- 1. 공리 감사 (프로젝트 안의 axiom 선언도 여기서 걸린다)
  let collect : CollectAxioms.M Unit := project.keys.forM CollectAxioms.collect
  let (_, s) := (collect.run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in s.axioms do
    unless allowed.contains ax do
      throwError "Unexpected axiom in the project dependency graph: {ax}"
  let theorems := project.fold (init := (0:Nat)) fun k _ ci => if ci matches .thmInfo _ then k + 1 else k

  logInfo m!"AXIOM AUDIT PASSED: {project.size} project declarations, {theorems} theorems; axioms = {s.axioms}"

  -- 2. 커널 재검사: 프로젝트 이외의 모듈만 불러온 환경에 프로젝트 선언을 다시 넣는다.
  -- `replay`는 컴파일러가 만드는 partial 보조 정의를 건너뛰지만, 재검사되는 선언 중
  -- 하나라도 그것에 의존하면 "unknown constant"로 실패하므로 정리에 영향을 줄 수 없다.
  let baseImports := env.header.moduleNames.filter (!isProjectModule ·)
    |>.map fun m => ({ module := m } : Import)
  let base ← importModules baseImports (← getOptions)
  let checked ← base.replay project
  for (n, ci) in project do
    unless ci.isPartial || (checked.toKernelEnv.find? n).isSome do
      throwError "Project constant was not replayed: {n}"
  logInfo m!"KERNEL REPLAY PASSED: all {project.size} project constants replayed (except compiler-generated partial helpers)"
