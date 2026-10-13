/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PerfectOpenApproximation

/-!
# Original perfect approximation regression statements

Records vanishing above a chosen cutoff for the homology of the restricted
original approximation cone, and strict perfectness of its source on the open.
The empty-open specialization retains an arbitrary input complex and cutoff.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace HomologicalComplex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
universe u
namespace QuillenTest.OriginalPerfectApproximation

/-- The chosen cutoff controls the actual original cone homology, not just a model. -/
theorem original_cone_vanishes_above_cutoff (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) (cutoff : ℤ) :
    ∃ (K P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K),
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj K)) ≅
        (toDerived W.toScheme).obj E) ∧
      ∀ i : ℤ, cutoff < i → IsZero
        (((restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))).homology i)
          := by
  obtain ⟨K, a, b, P, n, f, _, _, hP, hn, he, _, _, hle, _⟩ :=
    locallyPerfect_exists_original_strict_approximation R W hW E hE cutoff
  exact ⟨K, P, hP, f, he, fun i hi => (exactAt_iff_isZero_homology _ _).mp
    (CochainComplex.exactAt_of_isLE _ n i (lt_of_le_of_lt hn hi))⟩

/-- On the actual covered open the global finite-projective source is an original strict complex. -/
theorem original_strict_source_on_open (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) :
    ∃ (K P : ModuleComplex R) (_f : P ⟶ K),
      strictPerfect W.toScheme ((restrict W.ι).obj ((associatedComplex R).obj P)) ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj K)) ≅
        (toDerived W.toScheme).obj E) := by
  obtain ⟨K, a, b, P, n, f, _, _, hP, _, he, _⟩ :=
    locallyPerfect_exists_original_strict_approximation R W hW E hE 0
  exact ⟨K, P, f, strictPerfect_restrict W.ι (strictPerfect_associated R hP), he⟩

/-- Empty opens impose no nontrivial-ring or local-model premise on the original input. -/
theorem empty_open_original_input (R : CommRingCat.{u})
    (E : Complex (⊥ : (Spec R).Opens).toScheme) (cutoff : ℤ) :
    ∃ (K P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K),
      Nonempty ((toDerived (⊥ : (Spec R).Opens).toScheme).obj
        ((restrict (⊥ : (Spec R).Opens).ι).obj ((associatedComplex R).obj K)) ≅
        (toDerived (⊥ : (Spec R).Opens).toScheme).obj E) ∧
      ∀ i : ℤ, cutoff < i → IsZero
        (((restrict (⊥ : (Spec R).Opens).ι).obj
          ((associatedComplex R).obj (CochainComplex.mappingCone f))).homology i) := by
  apply original_cone_vanishes_above_cutoff R ⊥ (by simp) E _ cutoff
  intro x
  exact False.elim x.property

end QuillenTest.OriginalPerfectApproximation
