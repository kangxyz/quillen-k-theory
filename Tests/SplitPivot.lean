/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Algebra.ModuleComplex.SplitPivot
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Consumers of whole-complex split-pivot cancellation

These tests use the actual forward and backward chain maps to obtain
quasi-isomorphisms in both directions. The lower zero bound is tested together
with finiteness and projectivity at the upper pivot, without any noetherian
assumption or an assumed whole-complex homotopy.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Quillen.ModuleComplex.SplitPivot

namespace Quillen.Tests.SplitPivot

variable {R : Type u} [CommRing R] (C : CochainComplex (ModuleCat.{v} R) ℤ)
  (k : ℤ) (G : ModuleCat.{v} R)
  (s : C.X (k + 1) →ₗ[R] C.X k) (r : G →ₗ[R] C.X (k + 1))
  (t : C.X (k + 1) →ₗ[R] G)
  (hs : (C.d k (k + 1)).hom.comp s + r.comp t = LinearMap.id)

/-- Both specified chain maps preserve homology in every degree. -/
theorem original_maps_quasiIso :
    QuasiIso (forward C k G s r t hs) ∧ QuasiIso (backward C k G r) :=
  ⟨(homotopyEquiv C k G s r t hs).quasiIso_hom,
    (homotopyEquiv C k G s r t hs).quasiIso_inv⟩

include hs in
/-- The actual lower replacement remains projective and the upper term remains finite projective. -/
theorem replacement_pivot_terms
    [Module.Projective R (C.X k)] [Module.Projective R G] [Module.Finite R G] :
    Module.Projective R ((replacement C k G r).X k) ∧
      Module.Finite R ((replacement C k G r).X (k + 1)) ∧
      Module.Projective R ((replacement C k G r).X (k + 1)) := by
  let := projective_kernel C k G s r t hs
  exact ⟨Module.Projective.of_equiv (lowerIso C k G r).toLinearEquiv.symm,
    finite_replacement_upper C k G r, projective_replacement_upper C k G r⟩

include hs in
/-- A lower-bounded original complex has a lower-bounded actual homotopy-equivalent replacement. -/
theorem bounded_replacement (a : ℤ) (ha : a ≤ k)
    (hC : ∀ i, i < a → IsZero (C.X i)) :
    (∀ i, i < a → IsZero ((replacement C k G r).X i)) ∧
      Nonempty (HomotopyEquiv C (replacement C k G r)) :=
  ⟨replacement_preserves_lower_bound C k G r a ha hC,
    ⟨homotopyEquiv C k G s r t hs⟩⟩

end Quillen.Tests.SplitPivot
