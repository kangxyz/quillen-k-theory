/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HomotopyPullback.CompactComparison

/-!
# Compact pullback comparison regression tests

Keep arbitrary base-change parameters distinct from compact test families,
and retain complete original boundary points and paths.
-/
@[expose] public section


noncomputable section
open Quillen Quillen.HomotopyPullback
open scoped Topology unitInterval
universe u

section CompactComparison
variable {E B X : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]
  (p : C(E, B)) (f : C(X, B)) (hp : CompactHomotopyLiftingProperty p)

-- Only the test D is compact/locally compact. Every original zero-locus path value survives.
example {D : Type u} [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D]
    (b : C(D, HomotopyPullback p f)) (duration : C(D, unitInterval))
    (hfixed : ∀ x, duration x = 0 → ∀ t, (b x).val.2.2 t = p (b x).val.2.1) :
    ∃ c : C(D, {z : X × E // p z.2 = f z.1}),
      (∀ x, (c x).val.1 = (b x).val.1) ∧
      (∀ x, duration x = 0 → (c x).val.2 = (b x).val.2.1) ∧
      ∃ K : b.Homotopy ((strictPullbackInclusion p f).comp c),
        (∀ t x, (K (t, x)).val.1 = (b x).val.1) ∧
        (∀ t x, duration x = 0 → (K (t, x)).val.2.1 = (b x).val.2.1) ∧
        (∀ t x, duration x = 0 → ∀ s, (K (t, x)).val.2.2 s = (b x).val.2.2 s) := by
  obtain ⟨c, hc, hs, K, hK⟩ :=
    strictPullbackInclusion_compact_relative p f hp b duration hfixed
  refine ⟨c, hc, hs, K.toHomotopy, hK, ?_, ?_⟩
  · exact fun t x hx ↦ congrArg (fun z : HomotopyPullback p f ↦ z.val.2.1) (K.prop t x hx)
  · exact fun t x hx s ↦
      congrArg (fun z : HomotopyPullback p f ↦ z.val.2.2 s) (K.prop t x hx)

-- The complete conclusion also detects an empty actual strict pullback.
example [IsEmpty {z : X × E // p z.2 = f z.1}] : IsEmpty (HomotopyPullback p f) :=
  (strictPullbackInclusion_isWeakHomotopyEquivalence_of_compact p f hp).isEmpty_target

example (z : {z : X × E // p z.2 = f z.1}) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (strictPullbackInclusion p f) (x := z) rfl) :=
  (strictPullbackInclusion_isWeakHomotopyEquivalence_of_compact p f hp).homotopy_bijective z 0

-- The returned homotopy starts at the full input point and ends at the canonical constant path.
example {D : Type u} [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D]
    (b : C(D, HomotopyPullback p f)) (duration : C(D, unitInterval))
    (hfixed : ∀ x, duration x = 0 → ∀ t, (b x).val.2.2 t = p (b x).val.2.1) :
    ∃ c : C(D, {z : X × E // p z.2 = f z.1}),
      ∃ K : b.Homotopy ((strictPullbackInclusion p f).comp c),
        (∀ x s, (K (0, x)).val.2.2 s = (b x).val.2.2 s) ∧
        (∀ x s, (K (1, x)).val.2.2 s = f (c x).val.1) := by
  obtain ⟨c, _, _, K, _⟩ :=
    strictPullbackInclusion_compact_relative p f hp b duration hfixed
  refine ⟨c, K.toHomotopy, ?_, ?_⟩
  · intro x s
    exact congrArg (fun z : HomotopyPullback p f ↦ z.val.2.2 s) (K.toHomotopy.map_zero_left x)
  · intro x s
    exact congrArg (fun z : HomotopyPullback p f ↦ z.val.2.2 s) (K.toHomotopy.map_one_left x)
-- The base-change parameter remains arbitrary; compactness is required only of HLP tests.
example : CompactHomotopyLiftingProperty (strictBaseProjection p f) := hp.baseChange p f

-- The original full boundary track, including its source and stored path,
-- is retained in every dimension; this is literal equality of points.
example (n : ℕ)
    (a : C(CubicalTests.boundary.{u} n,{z : X × E // p z.2 = f z.1}))
    (b : C(CubicalTests.cube.{u} n,HomotopyPullback p f))
    (H : ((strictPullbackInclusion p f).comp a).Homotopy
      (b.comp (CubicalTests.boundaryInclusion n).hom)) :
    ∃ c : C(CubicalTests.cube.{u} n,{z : X × E // p z.2 = f z.1}),
      c.comp (CubicalTests.boundaryInclusion n).hom = a ∧
      ∃ K : ((strictPullbackInclusion p f).comp c).Homotopy b,
        ∀ (t : unitInterval) (z : CubicalTests.boundary.{u} n),
          K (t,z.val) = H (t,z) :=
  strictPullbackInclusion_finiteCubeHELP p f hp n a b H

end CompactComparison
