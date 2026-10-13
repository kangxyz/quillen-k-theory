/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRestrictionIso
public import Quillen.AlgebraicGeometry.PerfectComplexes.RestrictionFunctoriality
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedHom.OpenUnion

/-!
# Original support restrictions and coverwise vanishing

Actual open-image and inverse-image restriction isomorphisms retain the
original scheme maps and complex functors. They transport derived vanishing
on a prescribed open and detect it on any genuine open-immersion cover.
The compactness lemma concerns only the actual image of a compact open.
No perfectness, quasicoherence, or separation premise is needed for the
restriction and zero-detection statements.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard

/-- Original derived zero objects are detected under restriction along an
actual scheme isomorphism. -/
lemma isZero_toDerived_restrict_iff_of_isIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsIso j] [IsOpenImmersion j] (E : Complex X) :
    IsZero ((toDerived U).obj ((restrict j).obj E)) ↔ IsZero ((toDerived X).obj E) := by
  constructor
  · intro hz
    have hF := hz.of_iso ((derivedRestrictFactors j).app E)
    rw [IsZero.iff_id_eq_zero]
    apply (derivedRestrict j).map_injective
    rw [(derivedRestrict j).map_id, (derivedRestrict j).map_zero]
    exact hF.eq_of_src _ _
  · intro hz
    exact ((derivedRestrict j).map_isZero hz).of_iso ((derivedRestrictFactors j).app E).symm

/-- The actual open image, presented by the original composite immersion. -/
def supportImageOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (Z : X.Opens) : Y.Opens :=
  (Z.ι ≫ f).opensRange

lemma supportImageOpen_eq_image {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (Z : X.Opens) : supportImageOpen f Z = f ''ᵁ Z := by
  rw [supportImageOpen, Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]

lemma isCompact_supportImageOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (Z : X.Opens) (hZ : IsCompact (Z : Set X)) : IsCompact (supportImageOpen f Z : Set Y) := by
  let : CompactSpace Z.toScheme := isCompact_iff_compactSpace.mp hZ
  exact isCompact_range (Z.ι ≫ f).continuous

/-- The genuine source-image isomorphism retains the original immersion. -/
def supportImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (Z : X.Opens) :
    Z.toScheme ≅ (supportImageOpen f Z).toScheme :=
  (Z.ι ≫ f).isoOpensRange

@[reassoc (attr := simp)]
lemma supportImageIso_hom_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (Z : X.Opens) :
    (supportImageIso f Z).hom ≫ (supportImageOpen f Z).ι = Z.ι ≫ f :=
  (Z.ι ≫ f).isoOpensRange_hom_ι

/-- The complete original restriction comparison for a support image. -/
def supportImageRestrictionNatIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (Z : X.Opens) :
    restrict (supportImageOpen f Z).ι ⋙ restrict (supportImageIso f Z).hom ≅
      restrict f ⋙ restrict Z.ι :=
  restrictCompIso (supportImageIso f Z).hom (supportImageOpen f Z).ι ≪≫
    eqToIso (restrict_congr (supportImageIso_hom_ι f Z)) ≪≫ (restrictCompIso Z.ι f).symm

/-- Vanishing on the actual image is exactly vanishing of the original
restricted complex on the original support open. -/
lemma isZero_restrict_supportImage_iff {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (Z : X.Opens) (E : Complex Y) :
    IsZero ((toDerived (supportImageOpen f Z).toScheme).obj
      ((restrict (supportImageOpen f Z).ι).obj E)) ↔
    IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj ((restrict f).obj E))) := by
  rw [← isZero_toDerived_restrict_iff_of_isIso (supportImageIso f Z).hom]
  exact ((toDerived Z.toScheme).mapIso ((supportImageRestrictionNatIso f Z).app E)).isZero_iff
end Quillen.PerfectComplexes

namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard

lemma supportImageOpen_le_opensRange {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (Z : X.Opens) :
    supportImageOpen f Z ≤ f.opensRange := by
  rw [supportImageOpen_eq_image]
  exact f.image_le_opensRange Z

lemma supportImageIso_hom_inclusion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (Z : X.Opens) :
    (supportImageIso f Z).hom ≫ Y.homOfLE (supportImageOpen_le_opensRange f Z) =
      Z.ι ≫ f.isoOpensRange.hom := by
  apply (cancel_mono f.opensRange.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, supportImageIso_hom_ι,
    Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]

/-- Original restriction of the source after changing only its presentation
as the image open. -/
def supportImageSourceRestrictionIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (Z : X.Opens) (E : Complex X) :
    (restrict (supportImageIso f Z).hom).obj
      ((restrict (Y.homOfLE (supportImageOpen_le_opensRange f Z))).obj
        ((restrict f.isoOpensRange.inv).obj E)) ≅ (restrict Z.ι).obj E :=
  (restrictCompIso (supportImageIso f Z).hom
    (Y.homOfLE (supportImageOpen_le_opensRange f Z))).app _ ≪≫
  (restrictCompIso ((supportImageIso f Z).hom ≫
    Y.homOfLE (supportImageOpen_le_opensRange f Z)) f.isoOpensRange.inv).app E ≪≫
  (eqToIso (restrict_congr (by
    rw [supportImageIso_hom_inclusion, Category.assoc, Iso.hom_inv_id, Category.comp_id]))).app E

lemma isZero_restrict_image_source_iff {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (Z : X.Opens) (E : Complex X) :
    IsZero ((toDerived (supportImageOpen f Z).toScheme).obj
      ((restrict (Y.homOfLE (supportImageOpen_le_opensRange f Z))).obj
        ((restrict f.isoOpensRange.inv).obj E))) ↔
    IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj E)) := by
  rw [← isZero_toDerived_restrict_iff_of_isIso (supportImageIso f Z).hom]
  exact ((toDerived Z.toScheme).mapIso (supportImageSourceRestrictionIso f Z E)).isZero_iff
end Quillen.PerfectComplexes

namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard

/-- Original derived zero objects are detected by any actual covering family
of open immersions. -/
lemma isZero_toDerived_of_openImmersionCover {X : Scheme.{u}} (E : Complex X)
    {ι : Type*} (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i, ∃ y, j i y = x)
    (hz : ∀ i, IsZero ((toDerived (U i)).obj ((restrict (j i)).obj E))) :
    IsZero ((toDerived X).obj E) := by
  have hq : QuasiIso (0 : E ⟶ E) := by
    apply quasiIso_of_openImmersionCover _ U j hcover
    intro i
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso (U i).Modules _).mp
    exact (hz i).isIso (hz i) _
  have hi : IsIso ((toDerived X).map (0 : E ⟶ E)) := inferInstance
  rw [(toDerived X).map_zero] at hi
  exact (isIsoZero_iff_source_target_isZero _ _).mp hi |>.1

/-- The genuine restricted morphism of an open immersion is an open immersion. -/
instance supportResLE_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (Z : Y.Opens) (T : X.Opens) (h : T ≤ f ⁻¹ᵁ Z) :
    IsOpenImmersion (f.resLE Z T h) := by
  have : IsOpenImmersion (f.resLE Z T h ≫ Z.ι) := by
    rw [f.resLE_comp_ι h]
    infer_instance
  exact IsOpenImmersion.of_comp _ Z.ι

/-- Actual restriction on the inverse-image support open, with the genuine
restricted scheme map. -/
def supportPreimageRestrictionIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (Z : Y.Opens) (E : Complex Y) :
    (restrict (f ⁻¹ᵁ Z).ι).obj ((restrict f).obj E) ≅
      (restrict (f.resLE Z (f ⁻¹ᵁ Z) le_rfl)).obj ((restrict Z.ι).obj E) :=
  (restrictCompIso (f ⁻¹ᵁ Z).ι f).app E ≪≫
    (eqToIso (restrict_congr (f.resLE_comp_ι le_rfl).symm)).app E ≪≫
    ((restrictCompIso (f.resLE Z (f ⁻¹ᵁ Z) le_rfl) Z.ι).app E).symm

/-- Vanishing on a fixed support open descends through actual geometric
restriction to its inverse image. -/
lemma isZero_restrict_preimage_of_isZero {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (Z : Y.Opens) (E : Complex Y)
    (hz : IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj E))) :
    IsZero ((toDerived (f ⁻¹ᵁ Z).toScheme).obj
      ((restrict (f ⁻¹ᵁ Z).ι).obj ((restrict f).obj E))) := by
  let q := f.resLE Z (f ⁻¹ᵁ Z) le_rfl
  have hq : IsZero ((toDerived (f ⁻¹ᵁ Z).toScheme).obj ((restrict q).obj ((restrict Z.ι).obj E))) :=
    ((derivedRestrict q).map_isZero hz).of_iso
      ((derivedRestrictFactors q).app ((restrict Z.ι).obj E)).symm
  exact hq.of_iso ((toDerived (f ⁻¹ᵁ Z).toScheme).mapIso (supportPreimageRestrictionIso f Z E))

/-- Coverwise vanishing on the actual inverse-image support opens detects
vanishing on the original global support open. -/
lemma isZero_restrict_of_openImmersionCover {X : Scheme.{u}} (E : Complex X) (Z : X.Opens)
    {ι : Type*} (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i, ∃ y, j i y = x)
    (hz : ∀ i, IsZero ((toDerived (j i ⁻¹ᵁ Z).toScheme).obj
      ((restrict (j i ⁻¹ᵁ Z).ι).obj ((restrict (j i)).obj E)))) :
    IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj E)) := by
  let V (i : ι) := (j i ⁻¹ᵁ Z).toScheme
  let q (i : ι) := (j i).resLE Z (j i ⁻¹ᵁ Z) le_rfl
  have : ∀ i, IsOpenImmersion (q i) := by intro i; dsimp [q]; infer_instance
  apply isZero_toDerived_of_openImmersionCover _ V q
  · intro x
    obtain ⟨i, y, hy⟩ := hcover (Z.ι x)
    have hyZ : y ∈ j i ⁻¹ᵁ Z := by
      change j i y ∈ Z
      rw [hy]
      exact x.property
    refine ⟨i, ⟨y, hyZ⟩, ?_⟩
    apply Z.ι.isOpenEmbedding.injective
    change (q i ≫ Z.ι) ⟨y, hyZ⟩ = Z.ι x
    rw [Scheme.Hom.resLE_comp_ι]
    exact hy
  · intro i
    exact (hz i).of_iso ((toDerived (V i)).mapIso (supportPreimageRestrictionIso (j i) Z E)).symm
end Quillen.PerfectComplexes
