import Quillen.Topology.HomotopyGroups.WeakEquivalenceProperty
import Quillen.Waldhausen.Fibration.AllWeak.CanonicalFiberFactorization
import Quillen.Topology.HomotopyFiber.CommonBaseSquare
import Quillen.Waldhausen.Fibration.AllWeak.RelativeInclusion
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.Waldhausen.Approximation.Properties
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.AllWeak.CanonicalFiberFactorization,
    `Quillen.Topology.HomotopyFiber.CommonBaseSquare]
  let mut counts : Array Nat := #[0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (· + 1)
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless counts == #[20,21] do throwError "Expected41 source origins, found {counts}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing defining module {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  logInfo m!"Audited all original fiber-square origins: {counts}"
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Topology
universe u v
section Generic
variable {C : Type u} [Category.{v} C] (W : Structure C)
example (x : W.Delooping) (t : unitInterval) :
    AllWeak.changeWeakNullhomotopy W (t,x) =
      AllWeak.contraction W (t,changeWeakMap (AllWeak.nested W) x) := rfl
example (x : W.Delooping) : (AllWeak.changeWeakFiberLift W x).1.1 = x := rfl
example (x : W.Delooping) (t : unitInterval) :
    (AllWeak.changeWeakFiberLift W x).1.2 t =
      AllWeak.contraction W (t,changeWeakMap (AllWeak.nested W) x) := rfl
example : (AllWeak.changeWeakFiberLiftEquiv W).toFun = AllWeak.changeWeakFiberLift W := rfl
example : (AllWeak.changeWeakFiberLiftEquiv W).invFun =
    HomotopyFiber.projection (changeWeakMap (AllWeak.nested W))
      (AllWeak.waldhausenStructure W).kBasepoint := AllWeak.changeWeakFiberLiftEquiv_invFun W
example : (HomotopyFiber.projection (changeWeakMap (AllWeak.nested W))
    (AllWeak.waldhausenStructure W).kBasepoint).comp (AllWeak.changeWeakFiberLift W) =
      ContinuousMap.id _ := rfl
example : AllWeak.changeWeakFiberLift W W.kBasepoint =
    HomotopyFiber.basepoint (changeWeakMap (AllWeak.nested W))
      (AllWeak.waldhausenStructure W).kBasepoint W.kBasepoint
        (changeWeakMap_basepoint (AllWeak.nested W)) := AllWeak.changeWeakFiberLift_basepoint W
example (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) (AllWeak.changeWeakFiberLift W)
      (x := W.kBasepoint) (AllWeak.changeWeakFiberLift_basepoint W)) :=
  AllWeak.changeWeakFiberLift_bijective W n
example : Function.Bijective
    (homotopyGroupMap (N := Fin 0) (AllWeak.changeWeakFiberLift W)
      (x := W.kBasepoint) (AllWeak.changeWeakFiberLift_basepoint W)) :=
  AllWeak.changeWeakFiberLift_bijective W 0
end Generic
section Canonical
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]
example : (AllWeak.acyclicFiberSquareMap N).comp
    (AllWeak.changeWeakFiberLift (acyclicStructure N)) = canonicalFiberMap N :=
  AllWeak.acyclicFiberSquareMap_changeWeakFiberLift N
example (x : (acyclicStructure N).Delooping) :
    (AllWeak.acyclicFiberSquareMap N
      (AllWeak.changeWeakFiberLift (acyclicStructure N) x)).1.1 = acyclicInclusionMap N x := rfl
example (x : (acyclicStructure N).Delooping) (t : unitInterval) :
    (AllWeak.acyclicFiberSquareMap N
      (AllWeak.changeWeakFiberLift (acyclicStructure N) x)).1.2 t =
      acyclicNullhomotopy N (t,x) := AllWeak.contraction_acyclicNullhomotopy N t x
example (z : HomotopyFiber (changeWeakMap (AllWeak.nested (acyclicStructure N)))
    (AllWeak.waldhausenStructure (acyclicStructure N)).kBasepoint) (t : unitInterval) :
    (AllWeak.acyclicFiberSquareMap N z).1.2 t =
      deloopingMap (AllWeak.acyclicInclusion_exact N) (z.1.2 t) := rfl
example : AllWeak.acyclicFiberSquareMap N
    (HomotopyFiber.basepoint (changeWeakMap (AllWeak.nested (acyclicStructure N)))
      (AllWeak.waldhausenStructure (acyclicStructure N)).kBasepoint (acyclicStructure N).kBasepoint
      (changeWeakMap_basepoint (AllWeak.nested (acyclicStructure N)))) =
    HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
      (changeWeakMap_basepoint N) := AllWeak.acyclicFiberSquareMap_basepoint N
example : (canonicalFiberMap N).Homotopic
    ((AllWeak.acyclicFiberSquareMap N).comp (AllWeak.changeWeakFiberLift (acyclicStructure N))) := by
  rw [AllWeak.acyclicFiberSquareMap_changeWeakFiberLift]
end Canonical
section Scheme
open GilletWaldhausen AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
local instance fiberFactorizationSchemeSaturated (X : Scheme.{u}) :
    (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.weq.HasTwoOutOfThreeProperty :=
  complexSubcategory_saturated _
example (X : Scheme.{u}) :
    (AllWeak.acyclicFiberSquareMap (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))).comp
      (AllWeak.changeWeakFiberLift
        (acyclicStructure (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)))) =
      canonicalFiberMap (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) :=
  AllWeak.acyclicFiberSquareMap_changeWeakFiberLift _
end Scheme

open scoped Simplicial
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

section IndependentLift
variable {C : Type u} [Category.{v} C] (W : Structure C)
example : IsWeakHomotopyEquivalence (AllWeak.changeWeakFiberLift W) :=
  isWeakHomotopyEquivalence_of_homotopyEquiv (AllWeak.changeWeakFiberLiftEquiv W)
example : ((AllWeak.changeWeakFiberLift W).comp
    (HomotopyFiber.projection (changeWeakMap (AllWeak.nested W))
      (AllWeak.waldhausenStructure W).kBasepoint)).Homotopic (ContinuousMap.id _) := by
  simpa only [AllWeak.changeWeakFiberLiftEquiv_toFun,AllWeak.changeWeakFiberLiftEquiv_invFun] using
    (AllWeak.changeWeakFiberLiftEquiv W).right_inv
end IndependentLift
section IndependentCommonBase
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (p : C(X,B)) (q : C(Y,B)) (j : C(X,Y)) (sq : q.comp j = p) (b : B)
example (z : HomotopyFiber p b) :
    (HomotopyFiber.commonBaseStrictPullbackHomeomorph p q j sq b).symm
      (HomotopyFiber.commonBaseStrictPullbackHomeomorph p q j sq b z) = z :=
  (HomotopyFiber.commonBaseStrictPullbackHomeomorph p q j sq b).symm_apply_apply z
example (z : {z : X × HomotopyFiber q b // HomotopyFiber.projection q b z.2 = j z.1}) :
    (HomotopyFiber.commonBaseStrictPullbackHomeomorph p q j sq b)
      ((HomotopyFiber.commonBaseStrictPullbackHomeomorph p q j sq b).symm z) = z :=
  (HomotopyFiber.commonBaseStrictPullbackHomeomorph p q j sq b).apply_symm_apply z
example : IsWeakHomotopyEquivalence (HomotopyFiber.commonBaseComparison p q j sq b) :=
  isWeakHomotopyEquivalence_of_homotopyEquiv (HomotopyFiber.commonBaseComparisonEquiv p q j sq b)
example (z : HomotopyFiber p b) (t : unitInterval) :
    (HomotopyFiber.commonBaseComparison p q j sq b z).1.2.2 t = j z.1.1 := rfl
end IndependentCommonBase
