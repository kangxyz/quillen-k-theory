import Lean.Util.CollectAxioms
import Quillen.Topology.Realization.TwoSidedBarFiberEquivalence
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.Topology.Realization.TwoSidedBarFiber,
    `Quillen.Topology.Realization.TwoSidedBarFiberEquivalence]
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
  unless seen.size == 2 do throwError "Missing defining module"
  unless count == 18 do throwError "Expected exactly 18 origins, found {count}"
  logInfo m!"Audited all {count} origins of the actual bar fiber pair."
noncomputable section
open CategoryTheory Quillen Quillen.TheoremA Quillen.TwoSidedBar
open scoped Simplicial Topology
universe u
variable {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J)
  (y : |diagonalSSet (bar J)|) (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y)
example : (dropFiberMap η y p).1.1 = SSet.toTop.map (dropMap H) p.1.1 := rfl
example : (dropFiberMap η y p).1.2 = (SSet.toTop.map (dropMap J)).hom.comp p.1.2 := rfl
example : (evaluationFiberMap η y p).1.1 = SSet.toTop.map (evaluationMap H) p.1.1 := rfl
example : (evaluationFiberMap η y p).1.2 = (SSet.toTop.map (evaluationMap J)).hom.comp p.1.2 := rfl
example : IsWeakHomotopyEquivalence (dropFiberMap η y) := dropFiberMap_isWeakHomotopyEquivalence η y
example : IsWeakHomotopyEquivalence (evaluationFiberMap η y) := evaluationFiberMap_isWeakHomotopyEquivalence η y
example (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) (dropFiberMap η y) (x := p) rfl) := dropFiberMap_bijective η y p n
example (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) (evaluationFiberMap η y) (x := p) rfl) := evaluationFiberMap_bijective η y p n
example : Function.Bijective
    (homotopyGroupMap (N := Fin 0) (dropFiberMap η y) (x := p) rfl) := dropFiberMap_bijective η y p 0
example : Function.Bijective
    (homotopyGroupMap (N := Fin 0) (evaluationFiberMap η y) (x := p) rfl) := evaluationFiberMap_bijective η y p 0
example (z : HomotopyFiber (SSet.toTop.map (diagonalMap η)).hom
    (SSet.toTop.map (evaluationMap J) y)) :
    ∃ a, Joined (evaluationFiberMap η y a) z :=
  (evaluationFiberMap_isWeakHomotopyEquivalence η y).component_surjective z
example (x : (diagonalSSet H) _⦋0⦌) :
    (barMap η).app (Opposite.op ⦋0⦌) (vertex H x) =
      vertex J ((diagonalMap η).app (Opposite.op ⦋0⦌) x) := rfl
example (x : (diagonalSSet H) _⦋0⦌) :
    SSet.toTop.map (evaluationMap H) (realizationPoint (vertex H x)) = realizationPoint x :=
  evaluationMap_realizationPoint x

example : (SSet.toTop.map (dropMap J)).hom.comp (SSet.toTop.map (barMap η)).hom =
    (SSet.toTop.map (replacementMap η)).hom.comp (SSet.toTop.map (dropMap H)).hom :=
  realizedDropSquare η
example : (SSet.toTop.map (evaluationMap J)).hom.comp (SSet.toTop.map (barMap η)).hom =
    (SSet.toTop.map (diagonalMap η)).hom.comp (SSet.toTop.map (evaluationMap H)).hom :=
  realizedEvaluationSquare η
example : (dropRealizationHomotopyEquiv indexProjection (liftedDiagram H)).toFun =
    (SSet.toTop.map (dropMap H)).hom := rfl
example : (evaluationRealizationHomotopyEquiv H).toFun =
    (SSet.toTop.map (evaluationMap H)).hom := rfl
example [IsEmpty (HomotopyFiber (SSet.toTop.map (barMap η)).hom y)] :
    IsEmpty (HomotopyFiber (SSet.toTop.map (replacementMap η)).hom (SSet.toTop.map (dropMap J) y)) :=
  (dropFiberMap_isWeakHomotopyEquivalence η y).isEmpty_target
example [IsEmpty (HomotopyFiber (SSet.toTop.map (barMap η)).hom y)] :
    IsEmpty (HomotopyFiber (SSet.toTop.map (diagonalMap η)).hom (SSet.toTop.map (evaluationMap J) y)) :=
  (evaluationFiberMap_isWeakHomotopyEquivalence η y).isEmpty_target
example (z : HomotopyFiber (SSet.toTop.map (replacementMap η)).hom (SSet.toTop.map (dropMap J) y)) :
    ∃ x, Joined (dropFiberMap η y x) z :=
  (dropFiberMap_isWeakHomotopyEquivalence η y).component_surjective z
example (x : |diagonalSSet (bar H)|) (hx : SSet.toTop.map (barMap η) x = y) :
    dropFiberMap η y (HomotopyFiber.basepoint _ y x hx) =
      HomotopyFiber.basepoint _ (SSet.toTop.map (dropMap J) y) (SSet.toTop.map (dropMap H) x)
        ((ContinuousMap.congr_fun (realizedDropSquare η) x).symm.trans
          (congrArg (SSet.toTop.map (dropMap J)) hx)) :=
  HomotopyFiber.map_basepoint (SSet.toTop.map (dropMap H)).hom
    (SSet.toTop.map (dropMap J)).hom (realizedDropSquare η) x y hx
example (x : |diagonalSSet (bar H)|) (hx : SSet.toTop.map (barMap η) x = y) :
    evaluationFiberMap η y (HomotopyFiber.basepoint _ y x hx) =
      HomotopyFiber.basepoint _ (SSet.toTop.map (evaluationMap J) y) (SSet.toTop.map (evaluationMap H) x)
        ((ContinuousMap.congr_fun (realizedEvaluationSquare η) x).symm.trans
          (congrArg (SSet.toTop.map (evaluationMap J)) hx)) :=
  HomotopyFiber.map_basepoint (SSet.toTop.map (evaluationMap H)).hom
    (SSet.toTop.map (evaluationMap J)).hom (realizedEvaluationSquare η) x y hx
