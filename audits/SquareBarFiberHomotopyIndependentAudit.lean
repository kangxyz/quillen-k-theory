import Quillen.Library
import Quillen.Topology.Realization.TwoSidedBarFiberHomotopyEquivalence
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.Topology.HomotopyFiber.SquareEquivalence,
    `Quillen.Topology.Realization.TwoSidedBarFiberHomotopyEquivalence]
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
  unless count == 18 do throwError "Expected 18 origins, found {count}"
  logInfo m!"Audited all {count} square/bar HE origins."
noncomputable section
open CategoryTheory Quillen
open scoped Simplicial Topology
universe u
section General
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]
  (p : C(X,A)) (q : C(Y,B))
  (e : ContinuousMap.HomotopyEquiv X Y) (eb : ContinuousMap.HomotopyEquiv A B)
  (sq : eb.toFun.comp p = q.comp e.toFun) (a : A)
example : (HomotopyPullback.comparisonHomotopyEquivOfEquivalences p q e eb sq).toFun =
    HomotopyPullback.comparison q eb.toFun p e.toFun sq.symm := rfl
example : (HomotopyPullback.comparisonFiberHomotopyEquivOfEquivalences p q e eb sq a).toFun =
    HomotopyPullback.comparisonFiber p q e.toFun eb.toFun sq.symm a := rfl
example : (HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq a).toFun =
    HomotopyFiber.map e.toFun eb.toFun sq a := rfl
example (z : HomotopyFiber p a) :
    (HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq a z).val =
      (e z.val.1, eb.toFun.comp z.val.2) := rfl
example : ((HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq a).invFun.comp
    (HomotopyFiber.map e.toFun eb.toFun sq a)).Homotopic (ContinuousMap.id _) :=
  (HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq a).left_inv
example : ((HomotopyFiber.map e.toFun eb.toFun sq a).comp
    (HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq a).invFun).Homotopic
    (ContinuousMap.id _) := (HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq a).right_inv
example (z : HomotopyFiber p a) (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) (HomotopyFiber.map e.toFun eb.toFun sq a) (x := z) rfl) :=
  homotopyGroupMap_bijective_of_homotopyEquiv (HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq a) rfl n
example (z : HomotopyFiber p a) : Function.Bijective
    (homotopyGroupMap (N := Fin 0) (HomotopyFiber.map e.toFun eb.toFun sq a) (x := z) rfl) :=
  homotopyGroupMap_bijective_of_homotopyEquiv (HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq a) rfl 0
example [IsEmpty (HomotopyFiber p a)] : IsEmpty (HomotopyFiber q (eb a)) :=
  ⟨fun z ↦ isEmptyElim ((HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq a).invFun z)⟩
example : CompactHomotopyExtensionLiftingProperty (HomotopyFiber.map e.toFun eb.toFun sq a) :=
  compactHELP_of_homotopyEquiv (HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq a)
end General
section OriginalBar
open TwoSidedBar TheoremA
variable {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J)
  (y : |diagonalSSet (bar J)|)
example : (dropFiberHomotopyEquiv η y).toFun = dropFiberMap η y := rfl
example : (evaluationFiberHomotopyEquiv η y).toFun = evaluationFiberMap η y := rfl
example (z : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (dropFiberHomotopyEquiv η y z).val =
      (SSet.toTop.map (dropMap H) z.val.1, (SSet.toTop.map (dropMap J)).hom.comp z.val.2) := rfl
example (z : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (evaluationFiberHomotopyEquiv η y z).val =
      (SSet.toTop.map (evaluationMap H) z.val.1,
       (SSet.toTop.map (evaluationMap J)).hom.comp z.val.2) := rfl
example : CompactHomotopyExtensionLiftingProperty (dropFiberMap η y) :=
  compactHELP_of_homotopyEquiv (dropFiberHomotopyEquiv η y)
example : CompactHomotopyExtensionLiftingProperty (evaluationFiberMap η y) :=
  compactHELP_of_homotopyEquiv (evaluationFiberHomotopyEquiv η y)
example : ((dropFiberHomotopyEquiv η y).invFun.comp (dropFiberMap η y)).Homotopic
    (ContinuousMap.id _) := (dropFiberHomotopyEquiv η y).left_inv
example : ((evaluationFiberMap η y).comp (evaluationFiberHomotopyEquiv η y).invFun).Homotopic
    (ContinuousMap.id _) := (evaluationFiberHomotopyEquiv η y).right_inv
end OriginalBar
