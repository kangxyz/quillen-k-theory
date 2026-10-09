import Quillen.Library
import Lean.Util.CollectAxioms
import Quillen.Topology.HomotopyPullback.WeakCoproduct
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.Topology.HomotopyFiber.WeakCoproduct,
    `Quillen.Topology.HomotopyPullback.WeakCoproduct]
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
  unless count == 6 do throwError "Expected 6 declarations, found {count}"
  logInfo m!"Audited all {count} origins of weak coproduct assembly."
noncomputable section
open Quillen Quillen.TheoremB.SkeletalCartesian
open scoped Topology
universe u
section Fibers
variable {ι : Type u} {X Y : ι → Type u}
  [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
  (f : ∀ i, C(X i,Y i)) (hf : ∀ i, IsWeakHomotopyEquivalence (f i))
example (i : ι) (y : Y i) : HomotopyFiber (f i) y ≃ₜ HomotopyFiber (sigmaMap f) ⟨i,y⟩ :=
  WeakCoproduct.fiberHomeomorph f i y
example (i : ι) (y : Y i) (z : HomotopyFiber (f i) y) :
    (WeakCoproduct.fiberHomeomorph f i y z).1.1 = ⟨i,z.1.1⟩ := rfl
example (i : ι) (y : Y i) (z : HomotopyFiber (f i) y) :
    (WeakCoproduct.fiberHomeomorph f i y z).1.2 = (ContinuousMap.sigmaMk i).comp z.1.2 := rfl
example : IsWeakHomotopyEquivalence (sigmaMap f) := WeakCoproduct.isWeakHomotopyEquivalence_sigma f hf
example (x : Σ i, X i) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (sigmaMap f) (x := x) rfl) :=
  (WeakCoproduct.isWeakHomotopyEquivalence_sigma f hf).homotopy_bijective x n
example (x : Σ i, X i) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (sigmaMap f) (x := x) rfl) :=
  (WeakCoproduct.isWeakHomotopyEquivalence_sigma f hf).homotopy_bijective x 0
example [IsEmpty ι] : IsWeakHomotopyEquivalence (sigmaMap f) :=
  WeakCoproduct.isWeakHomotopyEquivalence_sigma f (fun i ↦ isEmptyElim i)
example [∀ i, IsEmpty (X i)] : IsEmpty (Σ i, Y i) :=
  (WeakCoproduct.isWeakHomotopyEquivalence_sigma f hf).isEmpty_target
example (y : Σ i, Y i) : ∃ x, Joined (sigmaMap f x) y :=
  (WeakCoproduct.isWeakHomotopyEquivalence_sigma f hf).component_surjective y
end Fibers
section Squares
variable {ι : Type u} {X A : ι → Type u}
  [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (A i)]
  {E T : Type u} [TopologicalSpace E] [TopologicalSpace T]
  (q : C(E,T)) (s : ∀ i, C(A i,T)) (p : ∀ i, C(X i,A i)) (t : ∀ i, C(X i,E))
  (w : ∀ i, q.comp (t i) = (s i).comp (p i))
example : HomotopyPullback.comparison q (ContinuousMap.sigma s) (sigmaMap p) (ContinuousMap.sigma t)
    (sigmaFixedSquare q s p t w) =
      (sigmaPullbackMap q s).comp (sigmaMap (fun i ↦ HomotopyPullback.comparison q (s i) (p i) (t i) (w i))) := rfl
example (h : ∀ i, IsWeakHomotopyEquivalence (HomotopyPullback.comparison q (s i) (p i) (t i) (w i))) :
    IsWeakHomotopyEquivalence (HomotopyPullback.comparison q (ContinuousMap.sigma s) (sigmaMap p)
      (ContinuousMap.sigma t) (sigmaFixedSquare q s p t w)) :=
  HomotopyPullback.comparison_sigma_isWeakHomotopyEquivalence q s p t w h
example [IsEmpty ι] :
    IsWeakHomotopyEquivalence (HomotopyPullback.comparison q (ContinuousMap.sigma s) (sigmaMap p)
      (ContinuousMap.sigma t) (sigmaFixedSquare q s p t w)) :=
  HomotopyPullback.comparison_sigma_isWeakHomotopyEquivalence q s p t w (fun i ↦ isEmptyElim i)
example (h : ∀ i, IsWeakHomotopyEquivalence (HomotopyPullback.comparison q (s i) (p i) (t i) (w i)))
    (x : Σ i, X i) : Function.Bijective (homotopyGroupMap (N := Fin 0)
      (HomotopyPullback.comparison q (ContinuousMap.sigma s) (sigmaMap p)
        (ContinuousMap.sigma t) (sigmaFixedSquare q s p t w)) (x := x) rfl) :=
  (HomotopyPullback.comparison_sigma_isWeakHomotopyEquivalence q s p t w h).homotopy_bijective x 0
example (h : ∀ i, IsWeakHomotopyEquivalence (HomotopyPullback.comparison q (s i) (p i) (t i) (w i)))
    (x : Σ i, X i) (n : ℕ) : Function.Bijective (homotopyGroupMap (N := Fin n)
      (HomotopyPullback.comparison q (ContinuousMap.sigma s) (sigmaMap p)
        (ContinuousMap.sigma t) (sigmaFixedSquare q s p t w)) (x := x) rfl) :=
  (HomotopyPullback.comparison_sigma_isWeakHomotopyEquivalence q s p t w h).homotopy_bijective x n
example (h : ∀ i, IsWeakHomotopyEquivalence (HomotopyPullback.comparison q (s i) (p i) (t i) (w i)))
    (z : HomotopyPullback q (ContinuousMap.sigma s)) :
    ∃ x, Joined (HomotopyPullback.comparison q (ContinuousMap.sigma s) (sigmaMap p)
      (ContinuousMap.sigma t) (sigmaFixedSquare q s p t w) x) z :=
  (HomotopyPullback.comparison_sigma_isWeakHomotopyEquivalence q s p t w h).component_surjective z
example (x : Σ i, X i) :
    (HomotopyPullback.comparison q (ContinuousMap.sigma s) (sigmaMap p)
      (ContinuousMap.sigma t) (sigmaFixedSquare q s p t w) x).1.1 = ⟨x.1, p x.1 x.2⟩ := rfl
example (x : Σ i, X i) :
    (HomotopyPullback.comparison q (ContinuousMap.sigma s) (sigmaMap p)
      (ContinuousMap.sigma t) (sigmaFixedSquare q s p t w) x).1.2.2 =
      ContinuousMap.const unitInterval (s x.1 (p x.1 x.2)) := rfl
end Squares
