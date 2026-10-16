/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalFreeExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedModuleReplacement
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction

/-! Semantic consumers of genuine finite-free principal-open descent. -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.ModuleComplex.PrincipalLocalization
open Quillen.PerfectComplexes.Affine
namespace QuillenTest.PrincipalFreeExtension

open Quillen

/-- Actual finite-free descent supplies a genuine K-projective model over the
original ring, not only a class or a localized differential relation. -/
theorem actual_projective_descended_complex {R : Type u} [CommRing R] (r : R)
    (K : CochainComplex (ModuleCat.{u} (Localization.Away r)) ℤ)
    (a b : ℤ) (hbound : ∀ i, i < a ∨ b < i → IsZero (K.X i))
    (hfree : ∀ i, Module.Free (Localization.Away r) (K.X i))
    (hfinite : ∀ i, Module.Finite (Localization.Away r) (K.X i)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ, P.IsKProjective ∧
      (∀ i, i < a ∨ b < i → IsZero (P.X i)) ∧
      Nonempty ((localize r (.up ℤ)).obj P ≅ K) := by
  obtain ⟨P, hP, hf, he⟩ := exists_bounded_finiteFree_complex_descent r K a b hbound hfree hfinite
  have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).mpr (fun i hi => hP i (Or.inr
    hi))
  have (i : ℤ) : Projective (P.X i) := by
    let := (hf i).1
    infer_instance
  exact ⟨P, CochainComplex.isKProjective_of_projective P b, hP, he⟩

/-- The same original term bounds are retained even for localization at zero;
no injectivity of the scalar localization map is smuggled into descent. -/
theorem zero_localization_preserves_original_bounds {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} (Localization.Away (0 : R))) ℤ)
    (hbound : ∀ i, i < -3 ∨ 2 < i → IsZero (K.X i))
    (hfree : ∀ i, Module.Free (Localization.Away (0 : R)) (K.X i))
    (hfinite : ∀ i, Module.Finite (Localization.Away (0 : R)) (K.X i)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i, i < -3 ∨ 2 < i → IsZero (P.X i)) ∧
      Nonempty ((localize (0 : R) (.up ℤ)).obj P ≅ K) := by
  obtain ⟨P, hP, _, he⟩ :=
    exists_bounded_finiteFree_complex_descent (0 : R) K (-3) 2 hbound hfree hfinite
  exact ⟨P, hP, he⟩

/-- The result lands in the honest image of the original all-perfect restriction,
using an actual geometric chain isomorphism. -/
theorem actual_perfect_restriction_image (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r))))
    (hfree : ∀ i, Module.Free (Localization.Away r)
      (((sectionsComplex (.of (Localization.Away r))).obj P.obj).X i)) :
    (perfectRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).essImage
      ((strictToPerfect _).obj P) := by
  obtain ⟨Q, ⟨e⟩⟩ := exists_principal_strict_extension_of_free_sections R r P hfree
  exact ⟨(strictToPerfect _).obj Q, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Extension really gives an original chain quasi-isomorphism, and its inverse,
without replacing the geometric restriction by a conditional comparison. -/
theorem actual_geometric_quasiIso_extension (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r))))
    (hfree : ∀ i, Module.Free (Localization.Away r)
      (((sectionsComplex (.of (Localization.Away r))).obj P.obj).X i)) :
    ∃ (Q : StrictPerfect (Spec R))
      (e : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj Q.obj ≅
        P.obj),
      QuasiIso e.hom ∧ QuasiIso e.inv := by
  obtain ⟨Q, ⟨e⟩⟩ := exists_principal_strict_extension_of_free_sections R r P hfree
  exact ⟨Q, e, inferInstance, inferInstance⟩

end QuillenTest.PrincipalFreeExtension
