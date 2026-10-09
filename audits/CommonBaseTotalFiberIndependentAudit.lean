import Quillen.Topology.HomotopyFiber.CommonBaseSquareTransport
import Quillen.Waldhausen.Fibration.AllWeak.TotalFiberSquare
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.Topology.HomotopyGroups.WeakEquivalenceProperty
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.HomotopyFiber.CommonBaseSquareTransport,
    `Quillen.Waldhausen.Fibration.RelativeRows.TotalFiber,
    `Quillen.Waldhausen.Fibration.AllWeak.TotalFiberSquare]
  let mut counts : Array Nat := #[0,0,0]
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
  unless counts == #[10,15,16] do throwError "Unexpected original counts {counts}"
  logInfo m!"Audited all original common-base transport and total-tail origins: {counts}"
noncomputable section
universe u
namespace Transport
open Quillen
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Maps
variable {F X Y B : Type u} [TopologicalSpace F] [TopologicalSpace X]
  [TopologicalSpace Y] [TopologicalSpace B]
  (q : C(Y,B)) (j : C(X,Y)) (b : B) (f : C(F,Y))
  (k : C(F,HomotopyFiber q b)) (hk : (HomotopyFiber.projection q b).comp k = f)
example (z : HomotopyPullback f j) :
    (HomotopyFiber.fiberModelPullbackMap q j b f k hk z).1.1 = z.1.1 := rfl
example (z : HomotopyPullback f j) :
    (HomotopyFiber.fiberModelPullbackMap q j b f k hk z).1.2.1 = k z.1.2.1 := rfl
example (z : HomotopyPullback f j) :
    (HomotopyFiber.fiberModelPullbackMap q j b f k hk z).1.2.2 = z.1.2.2 := rfl
example : HomotopyFiber.fiberModelPullbackMap q j b ((HomotopyFiber.projection q b).comp k) k rfl =
    HomotopyPullback.sourceMap j (HomotopyFiber.projection q b) k := rfl
example (h : IsWeakHomotopyEquivalence k) :
    IsWeakHomotopyEquivalence (HomotopyFiber.fiberModelPullbackMap q j b f k hk) :=
  HomotopyFiber.fiberModelPullbackMap_isWeakHomotopyEquivalence q j b f k hk h
end Maps
section Comparison
variable {A F X Y B : Type u} [TopologicalSpace A] [TopologicalSpace F]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (p : C(X,B)) (q : C(Y,B)) (j : C(X,Y)) (sq : q.comp j = p) (b : B)
  (a : C(A,X)) (f : C(F,Y)) (i : C(A,F)) (w : f.comp i = j.comp a)
  (k₀ : C(A,HomotopyFiber p b)) (k₁ : C(F,HomotopyFiber q b))
  (h₀ : (HomotopyFiber.projection p b).comp k₀ = a)
  (h₁ : (HomotopyFiber.projection q b).comp k₁ = f)
  (hc : (HomotopyFiber.mapOver p q j sq b).comp k₀ = k₁.comp i)
example : (HomotopyFiber.fiberModelPullbackMap q j b f k₁ h₁).comp
    (HomotopyPullback.comparison f j a i w) =
      (HomotopyFiber.commonBaseComparison p q j sq b).comp k₀ :=
  HomotopyFiber.fiberModelComparison_factorization p q j sq b a f i w k₀ k₁ h₀ h₁ hc
example (hk₀ : IsWeakHomotopyEquivalence k₀) (hk₁ : IsWeakHomotopyEquivalence k₁) :
    IsWeakHomotopyEquivalence (HomotopyPullback.comparison f j a i w) :=
  HomotopyFiber.fiberModelComparison_isWeakHomotopyEquivalence
    p q j sq b a f i w k₀ k₁ h₀ h₁ hc hk₀ hk₁
end Comparison
section ActualFiberModels
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (p : C(X,B)) (q : C(Y,B)) (j : C(X,Y)) (sq : q.comp j = p) (b : B)
-- The actual fibers supply both weak model maps unconditionally.
example : IsWeakHomotopyEquivalence (HomotopyFiber.commonBaseComparison p q j sq b) := by
  exact HomotopyFiber.fiberModelComparison_isWeakHomotopyEquivalence p q j sq b
    (HomotopyFiber.projection p b) (HomotopyFiber.projection q b)
    (HomotopyFiber.mapOver p q j sq b) rfl
    (ContinuousMap.id _) (ContinuousMap.id _) rfl rfl rfl
    (isWeakHomotopyEquivalence_id _) (isWeakHomotopyEquivalence_id _)
end ActualFiberModels

end Transport
namespace Relative
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Topology Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)
example : RelativeRows.totalFiberInclusion N ≫ TheoremA.diagonalMap (RelativeRows.tailSRows N) =
    SSet.const (RelativeRows.ordinaryTotalZeroVertex (acyclicStructure N)) :=
  RelativeRows.totalFiberInclusion_tail N
example : RelativeRows.totalTailMap N =
    (SSet.toTop.map (TheoremA.diagonalMap (RelativeRows.tailSRows N))).hom := rfl
example (x : V.Delooping) :
    RelativeRows.totalTailMap N (SSet.toTop.map (RelativeRows.totalFiberInclusion N) x) =
      RelativeRows.ordinaryTotalBasepoint (acyclicStructure N) :=
  RelativeRows.totalTailMap_totalFiberInclusion N x
example (x : V.Delooping) : (RelativeRows.totalTailFiberComparison N x).1.1 =
    SSet.toTop.map (RelativeRows.totalFiberInclusion N) x := rfl
example (x : V.Delooping) : (RelativeRows.totalTailFiberComparison N x).1.2 =
    ContinuousMap.const unitInterval (RelativeRows.ordinaryTotalBasepoint (acyclicStructure N)) := rfl
example (x : V.Delooping) (t : unitInterval) : (RelativeRows.totalTailFiberComparison N x).1.2 t =
    RelativeRows.ordinaryTotalBasepoint (acyclicStructure N) := rfl
example : RelativeRows.totalTailFiberComparison N V.kBasepoint =
    HomotopyFiber.basepoint (RelativeRows.totalTailMap N)
      (RelativeRows.ordinaryTotalBasepoint (acyclicStructure N)) (RelativeRows.totalBasepoint N)
      (RelativeRows.totalTailMap_basepoint N) := RelativeRows.totalTailFiberComparison_basepoint N
example (W : Structure C) : (AllWeak.ordinaryTotalHomeomorph W : C(
    |TheoremA.diagonalSSet (RelativeRows.ordinarySRows (acyclicStructure (AllWeak.nested W)))|,
    |TheoremA.diagonalSSet (RelativeRows.ordinarySRows W)|)) =
    (SSet.toTop.map (AllWeak.ordinaryDiagonalIso W).hom).hom := rfl
example (W : Structure C) :
    AllWeak.ordinaryTotalInclusionMap W
      (RelativeRows.ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested W))) =
        RelativeRows.ordinaryTotalBasepoint W := AllWeak.ordinaryTotalInclusionMap_basepoint W
example : (AllWeak.ordinaryTotalInclusionMap (acyclicStructure N)).comp
    (RelativeRows.totalTailMap (AllWeak.nested (acyclicStructure N))) =
      (RelativeRows.totalTailMap N).comp (AllWeak.relativeTotalInclusionMap N) :=
  AllWeak.relativeTotalInclusion_tail N
example : (AllWeak.relativeTailFiberMap N).comp
    (RelativeRows.totalTailFiberComparison (AllWeak.nested (acyclicStructure N))) =
      (RelativeRows.totalTailFiberComparison N).comp (acyclicInclusionMap N) :=
  AllWeak.relativeTailFiberMap_totalTailFiberComparison N
example (z : HomotopyFiber (RelativeRows.totalTailMap (AllWeak.nested (acyclicStructure N)))
    (RelativeRows.ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested (acyclicStructure N))))) :
    (AllWeak.relativeTailFiberMap N z).1.1 = AllWeak.relativeTotalInclusionMap N z.1.1 := rfl
example (z : HomotopyFiber (RelativeRows.totalTailMap (AllWeak.nested (acyclicStructure N)))
    (RelativeRows.ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested (acyclicStructure N))))) :
    (AllWeak.relativeTailFiberMap N z).1.2 =
      (AllWeak.ordinaryTotalInclusionMap (acyclicStructure N)).comp z.1.2 := rfl
example (x : (acyclicStructure N).Delooping) (t : unitInterval) :
    (AllWeak.relativeTailFiberMap N
      (RelativeRows.totalTailFiberComparison (AllWeak.nested (acyclicStructure N)) x)).1.2 t =
      RelativeRows.ordinaryTotalBasepoint (acyclicStructure N) :=
  AllWeak.ordinaryTotalInclusionMap_basepoint (acyclicStructure N)
example (W : Structure C) :
    RelativeRows.ordinaryTotalZeroVertex W =
      zeroSimplex (QuotientRows.waldhausenStructure W ⦋0⦌).cof
        (QuotientRows.waldhausenStructure W ⦋0⦌).weq
        (QuotientRows.zero W ⦋0⦌) (QuotientRows.isZero W ⦋0⦌) (op ⦋0⦌) := rfl

end Relative

namespace Independent
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Topology Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section TransportPoints
variable {F X Y B : Type u} [TopologicalSpace F] [TopologicalSpace X]
  [TopologicalSpace Y] [TopologicalSpace B]
  (q : C(Y,B)) (j : C(X,Y)) (b : B) (f : C(F,Y))
  (k : C(F,HomotopyFiber q b)) (hk : (HomotopyFiber.projection q b).comp k = f)
example (z : HomotopyPullback f j) (t : unitInterval) :
    (HomotopyFiber.fiberModelPullbackMap q j b f k hk z).1.2.2 t = z.1.2.2 t := rfl
example (z : HomotopyPullback f j) :
    (HomotopyFiber.fiberModelPullbackMap q j b f k hk z).1.2.1.1.2 =
      (k z.1.2.1).1.2 := rfl
end TransportPoints
section OriginalPoints
variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)
example : (HomotopyFiber.projection (RelativeRows.totalTailMap N)
    (RelativeRows.ordinaryTotalBasepoint (acyclicStructure N))).comp
      (RelativeRows.totalTailFiberComparison N) =
        (SSet.toTop.map (RelativeRows.totalFiberInclusion N)).hom := rfl
example : AllWeak.relativeTailFiberMap N
    (HomotopyFiber.basepoint (RelativeRows.totalTailMap (AllWeak.nested (acyclicStructure N)))
      (RelativeRows.ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested (acyclicStructure N))))
      (RelativeRows.totalBasepoint (AllWeak.nested (acyclicStructure N)))
      (RelativeRows.totalTailMap_basepoint (AllWeak.nested (acyclicStructure N)))) =
    HomotopyFiber.basepoint (RelativeRows.totalTailMap N)
      (RelativeRows.ordinaryTotalBasepoint (acyclicStructure N))
      (RelativeRows.totalBasepoint N) (RelativeRows.totalTailMap_basepoint N) :=
  AllWeak.relativeTailFiberMap_basepoint N
example (W : Structure C) (x : |TheoremA.diagonalSSet
    (RelativeRows.ordinarySRows (acyclicStructure (AllWeak.nested W)))|) :
    (AllWeak.ordinaryTotalHomeomorph W).symm (AllWeak.ordinaryTotalInclusionMap W x) = x :=
  (AllWeak.ordinaryTotalHomeomorph W).symm_apply_apply x
example (W : Structure C) (x : |TheoremA.diagonalSSet (RelativeRows.ordinarySRows W)|) :
    AllWeak.ordinaryTotalInclusionMap W ((AllWeak.ordinaryTotalHomeomorph W).symm x) = x :=
  (AllWeak.ordinaryTotalHomeomorph W).apply_symm_apply x
example (W : Structure C) :
    (AllWeak.ordinaryTotalHomeomorph W).symm (RelativeRows.ordinaryTotalBasepoint W) =
      RelativeRows.ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested W)) := by
  rw [← AllWeak.ordinaryTotalInclusionMap_basepoint W]
  exact (AllWeak.ordinaryTotalHomeomorph W).symm_apply_apply _
example (z : HomotopyFiber (RelativeRows.totalTailMap (AllWeak.nested (acyclicStructure N)))
    (RelativeRows.ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested (acyclicStructure N)))))
    (t : unitInterval) :
    (AllWeak.relativeTailFiberMap N z).1.2 t =
      AllWeak.ordinaryTotalInclusionMap (acyclicStructure N) (z.1.2 t) := rfl
example (x : (acyclicStructure N).Delooping) :
    (AllWeak.relativeTailFiberMap N
      (RelativeRows.totalTailFiberComparison (AllWeak.nested (acyclicStructure N)) x)).1.1 =
      SSet.toTop.map (RelativeRows.totalFiberInclusion N) (acyclicInclusionMap N x) := by
  exact congrArg (fun z ↦ z.1.1)
    (ContinuousMap.congr_fun (AllWeak.relativeTailFiberMap_totalTailFiberComparison N) x)
example : RelativeRows.totalTailMap N (RelativeRows.totalBasepoint N) =
    RelativeRows.ordinaryTotalBasepoint (acyclicStructure N) :=
  RelativeRows.totalTailMap_basepoint N
end OriginalPoints
end Independent
