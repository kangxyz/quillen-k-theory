/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.OpenBaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.StructureSheafCohomology
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.Injective.RestrictionSections
public import Aglib.Topology.Sheaves.BasisExactness
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Actual direct images of the projective-line structure module

The canonical unit map into the original projection direct image is an isomorphism.
Its sections are the literal geometric ring-section maps. Higher right-derived direct
images vanish by restricting the given injective resolution through genuine coefficient
localization and detecting exactness on principal base opens. No quasicoherence of derived
direct images or commutation of sections with arbitrary sheaf homology is assumed.
All results hold over arbitrary commutative base rings, including the zero ring.
-/
@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.TwoOpen
variable {R S : CommRingCat.{u}} (f : R ⟶ S) [IsOpenImmersion (Spec.map f)]

lemma projection_unit_resolution_on_open_exact (I : InjectiveResolution
    (SheafOfModules.unit (twoChartLine R).ringCatSheaf)) (n : ℕ) :
    (((sectionsFunctor (twoChartLine R)
      ((projection R) ⁻¹ᵁ (Spec.map f).opensRange)).mapHomologicalComplex _).obj
        I.cocomplex).ExactAt (n + 1) := by
  let j := coefficientMap f
  let M : (twoChartLine R).Modules := SheafOfModules.unit (twoChartLine R).ringCatSheaf
  let J := restrictInjectiveResolution j M I
  let F := sectionsFunctor (twoChartLine S) ⊤
  have hz : IsZero ((F.rightDerived (n + 1)).obj (M.restrict j)) :=
    (isZero_rightDerived_structureSheaf_succ S n).of_iso
      ((F.rightDerived (n + 1)).mapIso (Scheme.Modules.restrictUnitIso j))
  have he : ((F.mapHomologicalComplex _).obj J.cocomplex).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hz.of_iso (J.isoRightDerivedObj F (n + 1)).symm
  rw [← coefficientMap_opensRange f]
  exact he.of_iso (restrictedSectionsComplexIso j I.cocomplex)

end AlgebraicGeometry.Scheme.ProjectiveLine

namespace AlgebraicGeometry.Scheme.ProjectiveLine
variable {R S : CommRingCat.{u}} (f : R ⟶ S) [IsOpenImmersion (Spec.map f)]

private lemma gammaIsoTop_inv {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (IsOpenImmersion.ΓIsoTop j).inv = j.appLE j.opensRange ⊤ (by simp) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.symm_inv,
    Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

lemma projection_open_sections_square :
    (projection R).appLE (Spec.map f).opensRange (coefficientMap f).opensRange
        (coefficientMap_opensRange f).le ≫ (IsOpenImmersion.ΓIsoTop (coefficientMap f)).inv =
      (IsOpenImmersion.ΓIsoTop (Spec.map f)).inv ≫ (projection S).appTop := by
  rw [gammaIsoTop_inv, gammaIsoTop_inv, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  simp [coefficientMap_projection]

instance projection_appTop_isIso (R : CommRingCat.{u}) : IsIso (projection R).appTop := by
  have h : (projection R).appTop = (Scheme.ΓSpecIso R).hom ≫ (globalSectionsIso R).hom := by
    rw [globalSectionsIso_hom, baseSections, Iso.hom_inv_id_assoc]
    rfl
  rw [h]
  infer_instance

lemma projection_open_app_isIso : IsIso ((projection R).app (Spec.map f).opensRange) := by
  have h : IsIso ((projection R).appLE (Spec.map f).opensRange
      (coefficientMap f).opensRange (coefficientMap_opensRange f).le ≫
        (IsOpenImmersion.ΓIsoTop (coefficientMap f)).inv) := by
    rw [projection_open_sections_square]
    infer_instance
  have hi : IsIso ((projection R).appLE (Spec.map f).opensRange
      (coefficientMap f).opensRange (coefficientMap_opensRange f).le) :=
    IsIso.of_isIso_comp_right _ (IsOpenImmersion.ΓIsoTop (coefficientMap f)).inv
  have he : homOfLE (coefficientMap_opensRange f).le = eqToHom (coefficientMap_opensRange f) :=
    Subsingleton.elim _ _
  let : IsIso (homOfLE (coefficientMap_opensRange f).le) := by rw [he]; infer_instance
  let : IsIso ((projection R).app (Spec.map f).opensRange ≫
      (twoChartLine R).presheaf.map (homOfLE (coefficientMap_opensRange f).le).op) := hi
  exact IsIso.of_isIso_comp_right ((projection R).app (Spec.map f).opensRange)
    ((twoChartLine R).presheaf.map (homOfLE (coefficientMap_opensRange f).le).op)

end AlgebraicGeometry.Scheme.ProjectiveLine

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.TwoOpen
variable (R : CommRingCat.{u})

lemma projection_unit_resolution_exact_succ
    (I : InjectiveResolution (SheafOfModules.unit (twoChartLine R).ringCatSheaf)) (n : ℕ) :
    (((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex _).obj
      I.cocomplex).ExactAt (n + 1) := by
  let K := ((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex _).obj I.cocomplex
  let F := SheafOfModules.toSheaf (Spec R).ringCatSheaf
  let : F.Faithful := inferInstanceAs (SheafOfModules.toSheaf (Spec R).ringCatSheaf).Faithful
  let : F.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteColimits F := ⟨fun _ ↦ inferInstance⟩
  let : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf (Spec R).ringCatSheaf))
  have h : ((F.mapHomologicalComplex _).obj K).ExactAt (n + 1) := by
    apply TopCat.Sheaf.exactAt_of_sections_on_basis _ _
      PrimeSpectrum.isBasis_basic_opens
    rintro U ⟨r, rfl⟩
    change (((sectionsFunctor (twoChartLine R)
      ((projection R) ⁻¹ᵁ PrimeSpectrum.basicOpen r)).mapHomologicalComplex _).obj
        I.cocomplex).ExactAt (n + 1)
    simpa only [Scheme.Hom.opensRange_localizationAway] using
      projection_unit_resolution_on_open_exact (R := R)
        (CommRingCat.ofHom (algebraMap R (Localization.Away r))) I n
  exact (ShortComplex.exact_map_iff_of_faithful (K.sc (n + 1)) F).mp h

lemma isZero_rightDerived_projection_unit_succ (n : ℕ) :
    IsZero (((Scheme.Modules.pushforward (projection R)).rightDerived (n + 1)).obj
      (SheafOfModules.unit (twoChartLine R).ringCatSheaf)) := by
  let M : (twoChartLine R).Modules := SheafOfModules.unit (twoChartLine R).ringCatSheaf
  let I := injectiveResolution M
  have h := projection_unit_resolution_exact_succ R I n
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp h).of_iso
    (I.isoRightDerivedObj (Scheme.Modules.pushforward (projection R)) (n + 1))

end AlgebraicGeometry.Scheme.ProjectiveLine

namespace AlgebraicGeometry.Scheme.ProjectiveLine
variable (R : CommRingCat.{u})

/-- The original canonical unit map into projection direct image. -/
def projectionUnitMap : SheafOfModules.unit (Spec R).ringCatSheaf ⟶
    (Scheme.Modules.pushforward (projection R)).obj
      (SheafOfModules.unit (twoChartLine R).ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit (projection R).toRingCatSheafHom

lemma projectionUnitMap_app (U : (Spec R).Opens) :
    Scheme.Modules.Hom.app (projectionUnitMap R) U =
      AddCommGrpCat.ofHom ((projection R).app U).hom.toAddMonoidHom := rfl

instance projectionUnitMap_isIso : IsIso (projectionUnitMap R) := by
  let F := SheafOfModules.toSheaf (Spec R).ringCatSheaf
  let : F.Faithful := inferInstanceAs (SheafOfModules.toSheaf (Spec R).ringCatSheaf).Faithful
  let : F.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteColimits F := ⟨fun _ ↦ inferInstance⟩
  let : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf (Spec R).ringCatSheaf))
  have hi : IsIso (F.map (projectionUnitMap R)) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis PrimeSpectrum.isBasis_basic_opens
    intro r
    have h : IsIso ((projection R).app (PrimeSpectrum.basicOpen r)) := by
      have hr := Scheme.Hom.opensRange_localizationAway (R := R) r
      rw [← hr]
      exact projection_open_app_isIso (R := R)
        (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
    change IsIso (AddCommGrpCat.ofHom
      ((projection R).app (PrimeSpectrum.basicOpen r)).hom.toAddMonoidHom)
    let e := (asIso ((projection R).app (PrimeSpectrum.basicOpen r))).commRingCatIsoToRingEquiv
    change IsIso (e.toAddEquiv.toAddCommGrpIso
      (X := AddCommGrpCat.of Γ(Spec R, PrimeSpectrum.basicOpen r))
      (Y := AddCommGrpCat.of Γ(twoChartLine R, (projection R) ⁻¹ᵁ
        PrimeSpectrum.basicOpen r))).hom
    infer_instance
  have : Mono (projectionUnitMap R) := F.mono_of_mono_map inferInstance
  have : Epi (projectionUnitMap R) := F.epi_of_epi_map inferInstance
  exact isIso_of_mono_of_epi _

/-- The structure module identified with its actual projection direct image. -/
def projectionUnitIso : SheafOfModules.unit (Spec R).ringCatSheaf ≅
    (Scheme.Modules.pushforward (projection R)).obj
      (SheafOfModules.unit (twoChartLine R).ringCatSheaf) := asIso (projectionUnitMap R)

end AlgebraicGeometry.Scheme.ProjectiveLine
