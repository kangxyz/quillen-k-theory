import Lean.Util.CollectAxioms
import Quillen.Topology.Realization.TwoSidedBarFiberHomotopyEquivalence
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
  unless count == 18 do throwError "Expected 18 declarations, found {count}"
  logInfo m!"Audited all {count} origins of original square/bar fiber homotopy equivalences."
noncomputable section
open Quillen CategoryTheory
open scoped Topology Simplicial
universe u
section Square
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]
  {p : C(X,A)} {q : C(Y,B)}
  (e : ContinuousMap.HomotopyEquiv X Y) (eb : ContinuousMap.HomotopyEquiv A B)
  (sq : eb.toFun.comp p = q.comp e.toFun) (a : A)
open HomotopyFiber
example : ContinuousMap.HomotopyEquiv (HomotopyFiber p a) (HomotopyFiber q (eb a)) :=
  mapHomotopyEquivOfEquivalences e eb sq a
example : (mapHomotopyEquivOfEquivalences e eb sq a).toFun = map e.toFun eb.toFun sq a := rfl
example (z : HomotopyFiber p a) :
    (mapHomotopyEquivOfEquivalences e eb sq a z).val.1 = e z.val.1 := rfl
example (z : HomotopyFiber p a) :
    (mapHomotopyEquivOfEquivalences e eb sq a z).val.2 = eb.toFun.comp z.val.2 := rfl
example : ((mapHomotopyEquivOfEquivalences e eb sq a).invFun.comp
    (map e.toFun eb.toFun sq a)).Homotopic (ContinuousMap.id (HomotopyFiber p a)) :=
  (mapHomotopyEquivOfEquivalences e eb sq a).left_inv
example : ((map e.toFun eb.toFun sq a).comp
    (mapHomotopyEquivOfEquivalences e eb sq a).invFun).Homotopic
      (ContinuousMap.id (HomotopyFiber q (eb a))) :=
  (mapHomotopyEquivOfEquivalences e eb sq a).right_inv
example (z : HomotopyFiber p a) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (map e.toFun eb.toFun sq a) (x := z) rfl) :=
  homotopyGroupMap_bijective_of_homotopyEquiv (mapHomotopyEquivOfEquivalences e eb sq a) rfl 0
example (z : HomotopyFiber p a) (n : ℕ) :
    (homotopyEquivPiEquiv (mapHomotopyEquivOfEquivalences e eb sq a) (x := z) rfl n).toMonoidHom =
      piMap n (map e.toFun eb.toFun sq a) (x := z) rfl := rfl
example [IsEmpty (HomotopyFiber p a)] : IsEmpty (HomotopyFiber q (eb a)) :=
  ⟨fun z ↦ isEmptyElim ((mapHomotopyEquivOfEquivalences e eb sq a).invFun z)⟩
example : (HomotopyPullback.comparisonHomotopyEquivOfEquivalences p q e eb sq).toFun =
    HomotopyPullback.comparison q eb.toFun p e.toFun sq.symm := rfl
example : (HomotopyPullback.comparisonFiberHomotopyEquivOfEquivalences p q e eb sq a).toFun =
    HomotopyPullback.comparisonFiber p q e.toFun eb.toFun sq.symm a := rfl
end Square
section Bar
open TwoSidedBar TheoremA
variable {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J)
  (y : |diagonalSSet (bar J)|)
example : (dropFiberHomotopyEquiv η y).toFun = dropFiberMap η y := rfl
example : (evaluationFiberHomotopyEquiv η y).toFun = evaluationFiberMap η y := rfl
example (z : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (dropFiberHomotopyEquiv η y z).val.2 =
      (SSet.toTop.map (dropMap J)).hom.comp z.val.2 := rfl
example (z : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (evaluationFiberHomotopyEquiv η y z).val.2 =
      (SSet.toTop.map (evaluationMap J)).hom.comp z.val.2 := rfl
example (z : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (dropFiberHomotopyEquiv η y z).val.1 = SSet.toTop.map (dropMap H) z.val.1 := rfl
example (z : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (evaluationFiberHomotopyEquiv η y z).val.1 = SSet.toTop.map (evaluationMap H) z.val.1 := rfl
example (z : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (dropFiberMap η y) (x := z) rfl) :=
  homotopyGroupMap_bijective_of_homotopyEquiv (dropFiberHomotopyEquiv η y) rfl 0
example (z : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (evaluationFiberMap η y) (x := z) rfl) :=
  homotopyGroupMap_bijective_of_homotopyEquiv (evaluationFiberHomotopyEquiv η y) rfl 0
end Bar
