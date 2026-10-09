import Lean.Util.CollectAxioms
import Quillen.Topology.Realization.TwoSidedBarEquivalence
open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`Quillen.Topology.Realization.TwoSidedBar,
    `Quillen.Topology.Realization.TwoSidedBarDrop,
    `Quillen.Topology.Realization.TwoSidedBarEvaluation,
    `Quillen.Topology.Realization.TwoSidedBarResolution,
    `Quillen.Topology.Realization.TwoSidedBarColumn,
    `Quillen.Topology.Realization.TwoSidedBarContraction,
    `Quillen.Topology.Realization.TwoSidedBarEquivalence]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    count := count + 1
    seen := seen.insert origin
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless seen.size == 7 do throwError "Missing defining module"
  unless count == 170 do throwError "Expected exactly 170 origins, found {count}"
  logInfo m!"Audited all {count} origins of the seven two-sided bar modules."
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Quillen Quillen.TheoremA Quillen.TwoSidedBar
open scoped Simplicial Topology
universe u
section Generic
variable {D : Type u} [SmallCategory D] (L : D ⥤ SimplexCategoryᵒᵖ) (H J : D ⥤ SSet.{u})
example : ContinuousMap.HomotopyEquiv |diagonalSSet (object L H)| |replacementDiagonal H| :=
  dropRealizationHomotopyEquiv L H
example : (dropRealizationHomotopyEquiv L H).toFun =
    (SSet.toTop.map (diagonalMap (drop L H))).hom := rfl
example (η : H ⟶ J) : map L η ≫ drop L J = drop L H ≫ simplicialReplacementMap η :=
  drop_naturality L η
end Generic
section Diagonal
variable (H J : SimplexCategoryᵒᵖ ⥤ SSet.{u})
example : ContinuousMap.HomotopyEquiv |diagonalSSet (bar H)| |diagonalSSet H| :=
  evaluationRealizationHomotopyEquiv H
example : (evaluationRealizationHomotopyEquiv H).toFun =
    (SSet.toTop.map (evaluationMap H)).hom := rfl
example (η : H ⟶ J) :
    diagonalMap (map indexProjection (Functor.whiskerLeft indexProjection η)) ≫ evaluationMap J =
      evaluationMap H ≫ diagonalMap η := evaluationMap_naturality η
example (x : (diagonalSSet H) _⦋0⦌) :
    (evaluationMap H).app (op ⦋0⦌) (vertex H x) = x := evaluationMap_vertex H x
example (x : (diagonalSSet H) _⦋0⦌) :
    (diagonalMap (drop indexProjection (liftedDiagram H))).app (op ⦋0⦌) (vertex H x) =
      ⟨(Functor.const (Fin 1)).obj (AsSmall.up.obj (op ⦋0⦌)), x⟩ := rfl
example (q : SimplexCategoryᵒᵖ) : nerve (Resolution H q) ≅ (bar H).flip.obj q := columnIso H q
example (q : SimplexCategoryᵒᵖ) :
    (resolutionEvaluationHomotopyEquiv H q).toFun =
      (classifyingSpaceMap (Resolution.evaluate H q)).hom := rfl
end Diagonal
