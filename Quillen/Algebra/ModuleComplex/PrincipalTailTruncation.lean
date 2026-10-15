/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.ProjectiveTailTruncation
public import Quillen.Algebra.ModuleComplex.PrincipalProjectiveLocality
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Global projective tail cutoff from actual principal-local models

Actual localization detects zero modules on a principal cover and commutes
with original opcycles and homology. Local tail homotopies therefore split the
localized boundary quotient, and proved finite-projective locality makes the
original boundary quotient finite projective. The literal global good
truncation is bounded finite-projective with the exact original upper bound;
its original projection is a quasi-isomorphism. No global homotopy model is
required, and the generating principal family need not be explicitly finite.
-/
@[expose] public section

open Quillen.CochainComplex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Quillen.ModuleComplex.PrincipalLocalization
variable {R : Type u} [CommRing R]

/-- Actual module localization on a principal cover detects zero objects,
without finiteness hypotheses. -/
theorem isZero_of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (M : ModuleCat.{u} R)
    (hM : ∀ r : s, IsZero (M.localizedModule (Submonoid.powers r.val))) : IsZero M := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y => ?_⟩
  apply Module.eq_of_isLocalized_span s hs
    (fun r => M.localizedModule (Submonoid.powers r.val))
    (fun r => M.localizedModuleMkLinearMap (Submonoid.powers r.val)) x y
  intro r
  exact (ModuleCat.isZero_iff_subsingleton.mp (hM r)).elim _ _

/-- The actual localized opcycles of a complex agree with opcycles of its
actual localized complex, via the original short-complex comparison. -/
def localizationOpcyclesIso (P : CochainComplex (ModuleCat.{u} R) ℤ) (r : R) (n : ℤ) :
    ((localize r (.up ℤ)).obj P).opcycles n ≅
      (P.opcycles n).localizedModule (Submonoid.powers r) :=
  (P.sc n).mapOpcyclesIso (ModuleCat.localizedModuleFunctor (Submonoid.powers r))

/-- Principal-local actual homotopy models split the boundary quotient locally;
proved finite-projective locality makes the original boundary quotient finite projective. -/
theorem finiteProjective_opcycles_of_principal_homotopy_models
    (s : Set R) (hs : Ideal.span s = ⊤)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hfinite : ∀ i, Module.Finite R (P.X i))
    (hprojective : ∀ i, Module.Projective R (P.X i))
    (hlocal : ∀ r : s, ∃ Q : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ,
      IsZero (Q.X n) ∧ Nonempty (HomotopyEquiv ((localize r.val (.up ℤ)).obj P) Q)) :
    Module.Finite R (P.opcycles n) ∧ Module.Projective R (P.opcycles n) := by
  apply finiteProjective_of_localizationSpan s hs (P.opcycles n)
  · intro r
    let := hfinite n
    let := finite_opcycles P n
    exact Module.Finite.of_isLocalizedModule (Submonoid.powers r.val)
      ((P.opcycles n).localizedModuleMkLinearMap (Submonoid.powers r.val))
  · intro r
    obtain ⟨Q, hQ, ⟨e⟩⟩ := hlocal r
    let := hprojective (n + 1)
    have hpr : Module.Projective (Localization.Away r.val)
        ((P.X (n + 1)).localizedModule (Submonoid.powers r.val)) :=
      Module.projective_of_isLocalizedModule (Submonoid.powers r.val)
        ((P.X (n + 1)).localizedModuleMkLinearMap (Submonoid.powers r.val))
    let : Module.Projective (Localization (Submonoid.powers r.val))
        (((localize r.val (.up ℤ)).obj P).X (n + 1)) := hpr
    have : Projective (((localize r.val (.up ℤ)).obj P).X (n + 1)) :=
      ModuleCat.projective_of_categoryTheory_projective _
    have : Projective (((localize r.val (.up ℤ)).obj P).opcycles n) :=
      projective_opcycles_of_homotopy_model e n hQ
    have : Projective ((P.opcycles n).localizedModule (Submonoid.powers r.val)) :=
      Projective.of_iso (localizationOpcyclesIso P r.val n) inferInstance
    exact ModuleCat.projective_of_module_projective _

/-- Local lower homotopy models imply the original global lower cohomology
bound, using genuine exact localization and actual zero detection. -/
theorem quasiIso_πTruncGE_of_principal_homotopy_models
    (s : Set R) (hs : Ideal.span s = ⊤)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hlocal : ∀ r : s, ∃ Q : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ,
      (∀ i, i < n → IsZero (Q.X i)) ∧
        Nonempty (HomotopyEquiv ((localize r.val (.up ℤ)).obj P) Q)) :
    QuasiIso (P.πTruncGE n) := by
  have : P.IsGE n := (CochainComplex.isGE_iff P n).mpr (fun i hi => by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    apply isZero_of_localizationSpan s hs
    intro r
    obtain ⟨Q, hQ, ⟨e⟩⟩ := hlocal r
    have : Q.IsStrictlyGE n := (CochainComplex.isStrictlyGE_iff Q n).mpr hQ
    have he : ((localize r.val (.up ℤ)).obj P).ExactAt i :=
      (exactAt_iff_of_quasiIsoAt e.hom i).mpr (Q.exactAt_of_isGE n i hi)
    have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp he
    exact hz.of_iso ((P.sc i).mapHomologyIso
      (ModuleCat.localizedModuleFunctor (Submonoid.powers r.val))).symm)
  infer_instance

/-- A principal-local bounded-below homotopy model suffices for a genuinely
global bounded finite-projective truncation of the original complex. The
original projection is quasi-isomorphic and keeps the exact bound `[n,b]`. -/
theorem bounded_finiteProjective_truncGE_of_principal_homotopy_models
    (s : Set R) (hs : Ideal.span s = ⊤)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n b : ℤ)
    (hbound : ∀ i, b < i → IsZero (P.X i))
    (hfinite : ∀ i, Module.Finite R (P.X i))
    (hprojective : ∀ i, Module.Projective R (P.X i))
    (hlocal : ∀ r : s, ∃ Q : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ,
      (∀ i, i < n+1 → IsZero (Q.X i)) ∧
        Nonempty (HomotopyEquiv ((localize r.val (.up ℤ)).obj P) Q)) :
    (∀ i, i < n ∨ b < i → IsZero ((P.truncGE n).X i)) ∧
      (∀ i, Module.Finite R ((P.truncGE n).X i) ∧
        Module.Projective R ((P.truncGE n).X i)) ∧ QuasiIso (P.πTruncGE n) := by
  have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff P b).mpr hbound
  have hop := finiteProjective_opcycles_of_principal_homotopy_models s hs P n hfinite hprojective
    (fun r => by
      obtain ⟨Q, hQ, he⟩ := hlocal r
      exact ⟨Q, hQ n (by omega), he⟩)
  refine ⟨fun i hi => ?_, fun i => ⟨finite_truncGE P n hfinite i, ?_⟩,
    quasiIso_πTruncGE_of_principal_homotopy_models s hs P n (fun r => ?_)⟩
  · rcases hi with hi | hi
    · exact (P.truncGE n).isZero_of_isStrictlyGE n i hi
    · exact (P.truncGE n).isZero_of_isStrictlyLE b i hi
  · rcases lt_trichotomy i n with hi | hi | hi
    · let := ModuleCat.isZero_iff_subsingleton.mp ((P.truncGE n).isZero_of_isStrictlyGE n i hi)
      infer_instance
    · subst i
      let := hop.2
      exact Module.Projective.of_equiv (P.truncGEXIsoOpcycles n).toLinearEquiv.symm
    · let := hprojective i
      exact Module.Projective.of_equiv (P.truncGEXIso n i hi).toLinearEquiv.symm
  · obtain ⟨Q, hQ, he⟩ := hlocal r
    exact ⟨Q, fun i hi => hQ i (by omega), he⟩

end Quillen.ModuleComplex.PrincipalLocalization
