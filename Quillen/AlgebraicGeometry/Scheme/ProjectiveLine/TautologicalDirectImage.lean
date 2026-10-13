/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalOpenBaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalCohomology
public import Quillen.CategoryTheory.Sites.BasisExactness
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# All actual direct images of the tautological line vanish

Original injective resolutions are restricted through genuine coefficient localization, retaining
the proved inclusion-preserving tautological comparison. Exactness is then detected on principal
base opens. Thus every original right-derived module-sheaf direct image, including degree zero,
vanishes for the actual projection over any commutative base ring.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf Quillen.SchemeSheaf.TwoOpen

lemma projection_tautological_resolution_on_open_exact {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)] (I : InjectiveResolution (tautologicalLine R)) (n : ℕ) :
    (((sectionsFunctor (twoChartLine R)
      ((projection R) ⁻¹ᵁ (Spec.map f).opensRange)).mapHomologicalComplex _).obj
        I.cocomplex).ExactAt n := by
  let j := coefficientMap f
  let J := restrictInjectiveResolution j (tautologicalLine R) I
  let F := sectionsFunctor (twoChartLine S) ⊤
  have hz : IsZero ((F.rightDerived n).obj ((tautologicalLine R).restrict j)) :=
    (isZero_rightDerived_tautologicalLine S n).of_iso
      ((F.rightDerived n).mapIso (tautologicalOpenIso f))
  have he : ((F.mapHomologicalComplex _).obj J.cocomplex).ExactAt n := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hz.of_iso (J.isoRightDerivedObj F n).symm
  rw [← coefficientMap_opensRange f]
  exact he.of_iso (restrictedSectionsComplexIso j I.cocomplex)

lemma projection_tautological_resolution_exact (R : CommRingCat.{u})
    (I : InjectiveResolution (tautologicalLine R)) (n : ℕ) :
    (((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex _).obj
      I.cocomplex).ExactAt n := by
  let K := ((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex _).obj I.cocomplex
  let F := SheafOfModules.toSheaf (Spec R).ringCatSheaf
  let : F.Faithful := inferInstanceAs (SheafOfModules.toSheaf (Spec R).ringCatSheaf).Faithful
  let : F.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteColimits F := ⟨fun _ ↦ inferInstance⟩
  let : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf (Spec R).ringCatSheaf))
  have h : ((F.mapHomologicalComplex _).obj K).ExactAt n := by
    apply Quillen.SheafCohomology.exactAt_of_sections_on_basis _ _
      PrimeSpectrum.isBasis_basic_opens
    rintro U ⟨r, rfl⟩
    change (((sectionsFunctor (twoChartLine R)
      ((projection R) ⁻¹ᵁ PrimeSpectrum.basicOpen r)).mapHomologicalComplex _).obj
        I.cocomplex).ExactAt n
    simpa only [Scheme.Hom.opensRange_localizationAway] using
      projection_tautological_resolution_on_open_exact (R := R)
        (CommRingCat.ofHom (algebraMap R (Localization.Away r))) I n
  exact (ShortComplex.exact_map_iff_of_faithful (K.sc n) F).mp h

lemma isZero_rightDerived_projection_tautologicalLine (R : CommRingCat.{u}) (n : ℕ) :
    IsZero (((Scheme.Modules.pushforward (projection R)).rightDerived n).obj
      (tautologicalLine R)) := by
  let I := injectiveResolution (tautologicalLine R)
  have h := projection_tautological_resolution_exact R I n
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp h).of_iso
    (I.isoRightDerivedObj (Scheme.Modules.pushforward (projection R)) n)

lemma isZero_pushforward_projection_tautologicalLine (R : CommRingCat.{u}) :
    IsZero ((Scheme.Modules.pushforward (projection R)).obj (tautologicalLine R)) :=
  (isZero_rightDerived_projection_tautologicalLine R 0).of_iso
    ((Scheme.Modules.pushforward (projection R)).rightDerivedZeroIsoSelf.app
      (tautologicalLine R)).symm

end Quillen.Scheme.ProjectiveLine
