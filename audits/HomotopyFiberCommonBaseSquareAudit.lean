import Quillen.Topology.HomotopyFiber.CommonBaseSquare
import Quillen.Waldhausen.Fibration.AllWeak.RelativeInclusion
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Topology.HomotopyFiber.CommonBaseSquare
  let mut count := 0
  for (name, _) in env.constants.toList do
    let some i := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[i.toNat]! == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count > 0 do throwError "Missing original source"
  logInfo m!"Audited all common-base-square origins: {count}"
noncomputable section
open Quillen
open scoped Topology Simplicial
universe u
section Generic
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (p : C(X,B)) (q : C(Y,B)) (j : C(X,Y)) (sq : q.comp j = p) (b : B)
example (z : HomotopyFiber p b) :
    (HomotopyFiber.commonBaseStrictPullbackHomeomorph p q j sq b z).1.1 = z.1.1 := rfl
example (z : HomotopyFiber p b) :
    (HomotopyFiber.commonBaseStrictPullbackHomeomorph p q j sq b z).1.2 =
      HomotopyFiber.mapOver p q j sq b z := rfl
example (z : HomotopyFiber p b) (t : unitInterval) :
    (HomotopyFiber.commonBaseStrictPullbackHomeomorph p q j sq b z).1.2.1.2 t = z.1.2 t := rfl
example (z : {z : X × HomotopyFiber q b // HomotopyFiber.projection q b z.2 = j z.1}) :
    ((HomotopyFiber.commonBaseStrictPullbackHomeomorph p q j sq b).symm z).1.1 = z.1.1 := rfl
example (z : {z : X × HomotopyFiber q b // HomotopyFiber.projection q b z.2 = j z.1}) :
    ((HomotopyFiber.commonBaseStrictPullbackHomeomorph p q j sq b).symm z).1.2 = z.1.2.1.2 := rfl
example : (HomotopyFiber.commonBaseComparisonEquiv p q j sq b).toFun =
    HomotopyPullback.comparison (HomotopyFiber.projection q b) j
      (HomotopyFiber.projection p b) (HomotopyFiber.mapOver p q j sq b) rfl := rfl
example (z : HomotopyFiber p b) :
    (HomotopyFiber.commonBaseComparison p q j sq b z).1.1 = z.1.1 := rfl
example (z : HomotopyFiber p b) :
    (HomotopyFiber.commonBaseComparison p q j sq b z).1.2.1 =
      HomotopyFiber.mapOver p q j sq b z := rfl
example (z : HomotopyFiber p b) (t : unitInterval) :
    (HomotopyFiber.commonBaseComparison p q j sq b z).1.2.1.1.2 t = z.1.2 t := rfl
example (z : HomotopyFiber p b) :
    (HomotopyFiber.commonBaseComparison p q j sq b z).1.2.2 =
      ContinuousMap.const unitInterval (j z.1.1) := rfl
example (z : HomotopyFiber p b) (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) (HomotopyFiber.commonBaseComparison p q j sq b) (x := z) rfl) :=
  HomotopyFiber.commonBaseComparison_bijective p q j sq b z n
example (z : HomotopyFiber p b) : Function.Bijective
    (homotopyGroupMap (N := Fin 0) (HomotopyFiber.commonBaseComparison p q j sq b) (x := z) rfl) :=
  HomotopyFiber.commonBaseComparison_bijective p q j sq b z 0
example (x : X) (hx : p x = b) (t : unitInterval) :
    (HomotopyFiber.commonBaseComparison p q j sq b (HomotopyFiber.basepoint p b x hx)).1.2.1.1.2 t = b := rfl
example (x : X) (hx : p x = b) :
    (HomotopyFiber.commonBaseComparison p q j sq b (HomotopyFiber.basepoint p b x hx)).1.2.2 =
      ContinuousMap.const unitInterval (j x) := rfl
end Generic
section ActualRelative
open CategoryTheory Waldhausen Waldhausen.Fibration
variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)
-- The original total inclusion is used literally; no relative fiber theorem enters.
example (b : |TheoremA.diagonalSSet (RelativeRows.ordinarySRows (acyclicStructure N))|) :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber
        ((SSet.toTop.map (TheoremA.diagonalMap (RelativeRows.tailSRows N))).hom.comp
          (SSet.toTop.map (AllWeak.relativeInclusionTotal N)).hom) b)
      (HomotopyPullback
        (HomotopyFiber.projection
          (SSet.toTop.map (TheoremA.diagonalMap (RelativeRows.tailSRows N))).hom b)
        (SSet.toTop.map (AllWeak.relativeInclusionTotal N)).hom) :=
  HomotopyFiber.commonBaseComparisonEquiv _ _ _ rfl b
end ActualRelative
