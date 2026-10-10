/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.DerivedHomVanishing
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedDerivedComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedModuleReplacement
public import Quillen.AlgebraicGeometry.PerfectComplexes.Closure

/-!
# Genuine affine derived Hom vanishing from actual term bounds

A bounded finite-projective module complex has no actual sheaf-derived maps
to a quasicoherent single placed below its original lower term bound. The
proof uses genuine module K-projectivity and the proved bounded affine
fullness of the original associated-derived functor. No projectivity or
finite generation is required of the target quasicoherent sheaf.

The original associated-derived and sheaf-localized endpoints are retained.
Actual principal restriction preserves the same bound; every integer source
shift costs exactly that integer in the displayed inequality. A genuine
supplied derived module model also yields vanishing for an arbitrary ambient
source, without restricting the original source terms or assuming a new
replacement theorem.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- The original associated-derived image has no maps to a single below its actual projective terms.
-/
lemma associatedDerivedHom_single_eq_zero_of_lower_terms (R : CommRingCat.{u})
    (P : ModuleComplex R) (hP : moduleStrictPerfect R P) (M : ModuleCat.{u} R)
    (a b : ℤ) (hbound : ∀ n, n < b → IsZero (P.X n)) (hab : a < b)
    (φ : (associatedDerived R).obj (DerivedCategory.Q.obj P) ⟶
      (associatedDerived R).obj (DerivedCategory.Q.obj
        ((_root_.CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj M))) : φ = 0 := by
  obtain ⟨l, c, hc⟩ := hP.1
  have : P.IsStrictlyGE b := (_root_.CochainComplex.isStrictlyGE_iff P b).mpr hbound
  have : P.IsStrictlyLE c := (_root_.CochainComplex.isStrictlyLE_iff P c).mpr
    (fun n hn => hc n (Or.inr hn))
  have : P.IsKProjective := isKProjective_of_moduleStrictPerfect R hP
  obtain ⟨ψ, rfl⟩ := (associatedDerived_bounded_map_bijective R
    (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj ((_root_.CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj M))
    b c a a).surjective φ
  rw [Quillen.CochainComplex.derivedHom_single_eq_zero_of_lower_terms P M a b hbound hab ψ,
    CategoryTheory.Functor.map_zero]

/-- Vanishing for the literal sheaf-localized associated complex and any quasicoherent single
  target. -/
lemma associatedComplex_derivedHom_single_eq_zero (R : CommRingCat.{u})
    (P : ModuleComplex R) (hP : moduleStrictPerfect R P)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (a b : ℤ) (hbound : ∀ n, n < b → IsZero (P.X n)) (hab : a < b)
    (φ : (toDerived (Spec R)).obj ((associatedComplex R).obj P) ⟶
      (toDerived (Spec R)).obj ((_root_.CochainComplex.singleFunctor (Spec R).Modules a).obj M)) :
    φ = 0 := by
  let A := moduleSpecΓFunctor.obj M
  let eP := (associatedDerivedFactors R).app P
  let eM : (associatedDerived R).obj (DerivedCategory.Q.obj
      ((_root_.CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj A)) ≅
      (toDerived (Spec R)).obj ((_root_.CochainComplex.singleFunctor (Spec R).Modules a).obj M) :=
    ((tilde.functor R).mapDerivedCategorySingleFunctor a).app A ≪≫
      (DerivedCategory.singleFunctor (Spec R).Modules a).mapIso (asIso M.fromTildeΓ)
  have h := associatedDerivedHom_single_eq_zero_of_lower_terms R P hP A a b hbound hab
    (eP.hom ≫ φ ≫ eM.inv)
  apply (cancel_mono eM.inv).mp
  apply (cancel_epi eP.hom).mp
  simpa only [Category.assoc, comp_zero, zero_comp] using h

/-- The same literal lower term bound survives every actual principal localization. -/
lemma principalRestriction_associated_derivedHom_single_eq_zero (R : CommRingCat.{u}) (r : R)
    (P : ModuleComplex R) (hP : moduleStrictPerfect R P)
    (M : (Spec (CommRingCat.of (Localization.Away r))).Modules) [M.IsQuasicoherent]
    (a b : ℤ) (hbound : ∀ n, n < b → IsZero (P.X n)) (hab : a < b)
    (φ : (toDerived (Spec (CommRingCat.of (Localization.Away r)))).obj
        ((restrict (CoherentScheme.principalOpen R r)).obj ((associatedComplex R).obj P)) ⟶
      (toDerived (Spec (CommRingCat.of (Localization.Away r)))).obj
        ((_root_.CochainComplex.singleFunctor (Spec (CommRingCat.of (Localization.Away r))).Modules
          a).obj M)) :
    φ = 0 := by
  let S := CommRingCat.of (Localization.Away r)
  let L := Quillen.ModuleComplex.PrincipalLocalization.localize r (.up ℤ)
  let e := (toDerived (Spec S)).mapIso ((principalRestrictionAssociatedComplexIso R r).app P)
  have h := associatedComplex_derivedHom_single_eq_zero S (L.obj P)
    (moduleStrictPerfect_localize R r hP) M a b
    (fun n hn => (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map_isZero (hbound n hn))
    hab (e.hom ≫ φ)
  apply (cancel_epi e.hom).mp
  simpa only [comp_zero] using h

/-- Affine strict-perfect sources retain their exact original lower term bound. -/
lemma strictPerfect_derivedHom_single_eq_zero (R : CommRingCat.{u})
    (P : Complex (Spec R)) (hP : strictPerfect (Spec R) P)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (a b : ℤ) (hbound : ∀ n, n < b → IsZero (P.X n)) (hab : a < b)
    (φ : (toDerived (Spec R)).obj P ⟶
      (toDerived (Spec R)).obj ((_root_.CochainComplex.singleFunctor (Spec R).Modules a).obj M)) :
    φ = 0 := by
  let e := (toDerived (Spec R)).mapIso (associatedSectionsIso R hP)
  have h := associatedComplex_derivedHom_single_eq_zero R ((sectionsComplex R).obj P)
    (moduleStrictPerfect_sections R hP) M a b
    (fun n hn => moduleSpecΓFunctor.map_isZero (hbound n hn)) hab (e.hom ≫ φ)
  apply (cancel_epi e.hom).mp
  simpa only [comp_zero] using h

/-- Every integer source shift retains the exact lower-term inequality a+n<b. -/
lemma strictPerfect_derivedHom_single_shift_eq_zero (R : CommRingCat.{u})
    (P : Complex (Spec R)) (hP : strictPerfect (Spec R) P)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (a b n : ℤ) (hbound : ∀ i, i < b → IsZero (P.X i)) (hab : a + n < b)
    (φ : ((toDerived (Spec R)).obj P)⟦n⟧ ⟶
      (toDerived (Spec R)).obj ((_root_.CochainComplex.singleFunctor (Spec R).Modules a).obj M)) :
    φ = 0 := by
  let e := ((toDerived (Spec R)).commShiftIso n).app P
  have h := strictPerfect_derivedHom_single_eq_zero R (P⟦n⟧) (strictPerfect_shift hP n)
    M a (b-n) (fun i hi =>
      (hbound (i+n) (by omega)).of_iso (P.shiftFunctorObjXIso n i (i+n) rfl))
    (by omega) (e.hom ≫ φ)
  apply (cancel_epi e.hom).mp
  simpa only [comp_zero] using h

/-- The actual principal restriction also permits every source shift with the same original bound.
-/
lemma principalRestriction_associated_derivedHom_single_shift_eq_zero
    (R : CommRingCat.{u}) (r : R) (P : ModuleComplex R) (hP : moduleStrictPerfect R P)
    (M : (Spec (CommRingCat.of (Localization.Away r))).Modules) [M.IsQuasicoherent]
    (a b n : ℤ) (hbound : ∀ i, i < b → IsZero (P.X i)) (hab : a + n < b)
    (φ : ((toDerived (Spec (.of (Localization.Away r)))).obj
        ((restrict (CoherentScheme.principalOpen R r)).obj ((associatedComplex R).obj P)))⟦n⟧ ⟶
      (toDerived (Spec (.of (Localization.Away r)))).obj
        ((_root_.CochainComplex.singleFunctor (Spec (.of (Localization.Away r))).Modules a).obj M))
          :
    φ = 0 := by
  apply strictPerfect_derivedHom_single_shift_eq_zero (.of (Localization.Away r)) _
    (strictPerfect_restrict _ (strictPerfect_associated R hP)) M a b n _ hab φ
  intro i hi
  exact (Scheme.Modules.restrictFunctor (CoherentScheme.principalOpen R r)).map_isZero
    ((tilde.functor R).map_isZero (hbound i hi))

/-- The genuine derived finite-projective model suffices; original source terms are unrestricted. -/
lemma derivedHom_single_eq_zero_of_module_model (R : CommRingCat.{u})
    (E : Derived (Spec R)) (P : ModuleComplex R) (hP : moduleStrictPerfect R P)
    (e : (toDerived (Spec R)).obj ((associatedComplex R).obj P) ≅ E)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (a b : ℤ) (hbound : ∀ n, n < b → IsZero (P.X n)) (hab : a < b)
    (φ : E ⟶ (toDerived (Spec R)).obj
      ((_root_.CochainComplex.singleFunctor (Spec R).Modules a).obj M)) : φ = 0 := by
  have h := associatedComplex_derivedHom_single_eq_zero R P hP M a b hbound hab (e.hom ≫ φ)
  apply (cancel_epi e.hom).mp
  simpa only [comp_zero] using h

end Quillen.PerfectComplexes.Affine
