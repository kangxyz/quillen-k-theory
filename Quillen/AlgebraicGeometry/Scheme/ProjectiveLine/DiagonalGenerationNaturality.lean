/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalGenerationEndpoints

/-!
# Naturality of the actual diagonal generation triangle

The original sheaf coefficient maps induce all three components of the triangle
map, including its connecting square. Identity and composition retain these maps.

The base ring is arbitrary, including the zero ring. These interfaces preserve
the accepted vector-bundle scope; they do not establish a projective-bundle
equivalence or a full coefficient extension.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
  DerivedCategory CategoryTheory.Pretriangulated

namespace CategoryTheory.ShortComplex.ShortExact
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)

/-- The bounded-below single triangle carries the actual map of short exact sequences. -/
def singleTrianglePlusMap : h₁.singleTrianglePlus ⟶ h₂.singleTrianglePlus :=
  DerivedCategory.Plus.ι.mapTriangle.preimage
    (h₁.singleTrianglePlusιIso.hom ≫ singleTriangle.map h₁ h₂ f ≫
      h₂.singleTrianglePlusιIso.inv)

@[simp] theorem singleTrianglePlusMap_hom₁ :
    (singleTrianglePlusMap h₁ h₂ f).hom₁ =
      (DerivedCategory.Plus.singleFunctor C 0).map f.τ₁ := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := congrArg TriangleMorphism.hom₁
    (DerivedCategory.Plus.ι.mapTriangle.map_preimage
      (h₁.singleTrianglePlusιIso.hom ≫ singleTriangle.map h₁ h₂ f ≫
        h₂.singleTrianglePlusιIso.inv))
  refine h.trans ?_
  dsimp [singleTrianglePlusιIso]
  simp only [Category.id_comp]
  change (singleFunctor C 0).map f.τ₁ ≫ 𝟙 _ = (singleFunctor C 0).map f.τ₁
  exact Category.comp_id _

@[simp] theorem singleTrianglePlusMap_hom₂ :
    (singleTrianglePlusMap h₁ h₂ f).hom₂ =
      (DerivedCategory.Plus.singleFunctor C 0).map f.τ₂ := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := congrArg TriangleMorphism.hom₂
    (DerivedCategory.Plus.ι.mapTriangle.map_preimage
      (h₁.singleTrianglePlusιIso.hom ≫ singleTriangle.map h₁ h₂ f ≫
        h₂.singleTrianglePlusιIso.inv))
  refine h.trans ?_
  dsimp [singleTrianglePlusιIso]
  simp only [Category.id_comp]
  change (singleFunctor C 0).map f.τ₂ ≫ 𝟙 _ = (singleFunctor C 0).map f.τ₂
  exact Category.comp_id _

@[simp] theorem singleTrianglePlusMap_hom₃ :
    (singleTrianglePlusMap h₁ h₂ f).hom₃ =
      (DerivedCategory.Plus.singleFunctor C 0).map f.τ₃ := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := congrArg TriangleMorphism.hom₃
    (DerivedCategory.Plus.ι.mapTriangle.map_preimage
      (h₁.singleTrianglePlusιIso.hom ≫ singleTriangle.map h₁ h₂ f ≫
        h₂.singleTrianglePlusιIso.inv))
  refine h.trans ?_
  dsimp [singleTrianglePlusιIso]
  simp only [Category.id_comp]
  change (singleFunctor C 0).map f.τ₃ ≫ 𝟙 _ = (singleFunctor C 0).map f.τ₃
  exact Category.comp_id _
end CategoryTheory.ShortComplex.ShortExact

namespace Quillen.SchemeSheaf
local instance naturalityStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- For any additive sheaf functor, its canonical single comparison is a natural
transformation, whether or not the derived unit is invertible. -/
def rightDerivedSingleComparison {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] :
    F ⋙ DerivedCategory.Plus.singleFunctor Y.Modules 0 ⟶
      DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙ F.rightDerivedFunctorPlus :=
  (isoWhiskerRight (exactSingleComplexNatIso F) DerivedCategory.Plus.Q).inv ≫
    whiskerLeft (CochainComplex.singleFunctorPlus X.Modules 0) F.rightDerivedFunctorPlusUnit
end Quillen.SchemeSheaf

namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf
local instance naturalityStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- The actual diagonal tensor comparison is natural in its original coefficient arrow. -/
theorem diagonalTensorPushforwardIso_naturality
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') (M : (twoChartLine R).Modules) :
    (moduleTensorRightFunctor (relativeSquare R)
      ((Scheme.Modules.pushforward (relativeDiagonal R)).obj M)).map
        ((Scheme.Modules.pullback (relativeFirst R)).map f) ≫
      (diagonalTensorPushforwardIso R E' M).hom =
    (diagonalTensorPushforwardIso R E M).hom ≫
      (Scheme.Modules.pushforward (relativeDiagonal R)).map
        ((moduleTensorRightFunctor (twoChartLine R) M).map f) := by
  let P := Scheme.Modules.pullback (relativeFirst R)
  let D := Scheme.Modules.pullback (relativeDiagonal R)
  let J := Scheme.Modules.pushforward (relativeDiagonal R)
  let T := moduleTensorRightFunctor (twoChartLine R) M
  let S := moduleTensorRightFunctor (relativeSquare R) (J.obj M)
  let e := sectionPullbackIso (relativeDiagonal R) (relativeFirst R)
    (relativeDiagonal_first R)
  have hp : S.map (P.map f) ≫ projectionFormulaMap (relativeDiagonal R) (P.obj E') M =
      projectionFormulaMap (relativeDiagonal R) (P.obj E) M ≫ J.map (T.map (D.map (P.map f))) :=
    (projectionFormulaNatTrans (relativeDiagonal R) M).naturality (P.map f)
  have hs : D.map (P.map f) ≫ e.hom.app E' = e.hom.app E ≫ f := e.hom.naturality f
  change S.map (P.map f) ≫ (projectionFormulaMap (relativeDiagonal R) (P.obj E') M ≫
      J.map (T.map (e.hom.app E'))) =
    (projectionFormulaMap (relativeDiagonal R) (P.obj E) M ≫ J.map (T.map (e.hom.app E))) ≫
      J.map (T.map f)
  rw [← Category.assoc, hp, Category.assoc, ← J.map_comp, ← T.map_comp, hs,
    T.map_comp, J.map_comp, Category.assoc]

/-- The actual diagonal derived single comparison respects original quotient-tensor arrows. -/
theorem diagonalQuotientTensorDerivedIso_naturality
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    (DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).map
      ((Scheme.Modules.pushforward (relativeDiagonal R)).map
        ((moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)).map f)) ≫
      (diagonalQuotientTensorDerivedIso R E').hom =
    (diagonalQuotientTensorDerivedIso R E).hom ≫
      (derivedPushforwardPlus (relativeDiagonal R)).map
        ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).map
          ((moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)).map f)) := by
  convert (rightDerivedSingleComparison
    (Scheme.Modules.pushforward (relativeDiagonal R))).naturality
      ((moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)).map f) using 1
        <;> rfl

/-- The existing fully-faithful third-vertex lift is exactly the canonical single
comparison followed by the original derived diagonal unit. -/
theorem diagonalTensorDerivedPlusIso_hom_eq
    (E : (twoChartLine R).Modules) [IsFiniteLocallyFree (twoChartLine R) E] :
    (diagonalTensorDerivedPlusIso R E).hom =
      (DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).map
        (diagonalTensorPushforwardIso R E (tautologicalQuotientLine R)).hom ≫
      (diagonalQuotientTensorDerivedIso R E).hom := by
  apply DerivedCategory.Plus.ι.map_injective
  dsimp only [diagonalTensorDerivedPlusIso, Functor.preimageIso]
  rw [Functor.map_preimage]
  simp [diagonalTensorSingleIso, diagonalSupportedDerivedVertexIso,
    singleFunctorIsoCompQ, singleZeroPlus]
  rfl

/-- The original diagonal-derived third vertex respects the actual coefficient tensor map. -/
theorem diagonalTensorDerivedPlusIso_naturality
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    (DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).map
      (diagonalBundleTensorSequenceMap R f).τ₃ ≫
      (diagonalTensorDerivedPlusIso R E').hom =
    (diagonalTensorDerivedPlusIso R E).hom ≫
      (derivedPushforwardPlus (relativeDiagonal R)).map
        ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).map
          ((moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)).map f)) := by
  rw [diagonalTensorDerivedPlusIso_hom_eq, diagonalTensorDerivedPlusIso_hom_eq]
  have hp := diagonalTensorPushforwardIso_naturality R f (tautologicalQuotientLine R)
  have hd := diagonalQuotientTensorDerivedIso_naturality R f
  rw [← Category.assoc, ← Functor.map_comp]
  erw [hp]
  rw [Functor.map_comp, Category.assoc, hd, Category.assoc]

/-- The actual full projected coefficient comparison, before transport of the triangle. -/
def diagonalCoefficientVertexComparison (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    (derivedPushforwardPlus (relativeSecond R)).obj (diagonalBundleTensorTrianglePlus R E).obj₃ ≅
      (diagonalCoefficientTensorTriangle R E).obj₃ :=
  (derivedPushforwardPlus (relativeSecond R)).mapIso (diagonalTensorDerivedPlusIso R E) ≪≫
    diagonalProjectedTensorVertexIso R E

/-- The full projected coefficient comparison sends the original diagonal tensor map
precisely to the original E tensor Q map. -/
theorem diagonalCoefficientVertexComparison_naturality
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    (derivedPushforwardPlus (relativeSecond R)).map
      ((DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).map
        (diagonalBundleTensorSequenceMap R f).τ₃) ≫
      (diagonalCoefficientVertexComparison R E').hom =
    (diagonalCoefficientVertexComparison R E).hom ≫
      (DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).map
        ((moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)).map f) := by
  have hd := diagonalTensorDerivedPlusIso_naturality R f
  have hs := (derivedDiagonalSecondIso R).hom.naturality
    ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).map
      ((moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)).map f))
  dsimp only [diagonalCoefficientVertexComparison, diagonalProjectedTensorVertexIso,
    Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, hd, Functor.map_comp, Category.assoc]
  erw [hs]
  simp only [Category.assoc, Functor.id_map]
  rfl

/-- The maintained coefficient triangle compared to the literal projected short-exact triangle. -/
def diagonalCoefficientToRawIso (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    diagonalCoefficientTensorTriangle R E ≅
      (derivedPushforwardPlus (relativeSecond R)).mapTriangle.obj
        (diagonalBundleTensorTrianglePlus R E) :=
  diagonalCoefficientTensorTriangleIso R E ≪≫
    (derivedPushforwardPlus (relativeSecond R)).mapTriangle.mapIso
      (diagonalDerivedTensorTrianglePlusIso R E)

/-- Transport the original map of short exact sequences through the maintained
coefficient identifications. This is an actual triangle morphism. -/
def diagonalCoefficientTensorTriangleMap
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    diagonalCoefficientTensorTriangle R E ⟶ diagonalCoefficientTensorTriangle R E' :=
  (diagonalCoefficientToRawIso R E).hom ≫
    (derivedPushforwardPlus (relativeSecond R)).mapTriangle.map
      (ShortComplex.ShortExact.singleTrianglePlusMap
        (diagonalBundleTensorSequence_shortExact R E)
        (diagonalBundleTensorSequence_shortExact R E') (diagonalBundleTensorSequenceMap R f)) ≫
      (diagonalCoefficientToRawIso R E').inv

@[simp] theorem diagonalCoefficientTensorTriangleMap_hom₁
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    (diagonalCoefficientTensorTriangleMap R f).hom₁ =
      (derivedPushforwardPlus (relativeSecond R)).map
        ((DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).map
          (diagonalBundleTensorSequenceMap R f).τ₁) := by
  simp only [diagonalCoefficientTensorTriangleMap, mapTriangle_obj, diagonalCoefficientToRawIso,
    diagonalCoefficientTensorTriangleIso, diagonalDerivedTensorTrianglePlusIso, Iso.trans_hom,
      Triangle.isoMk_hom,
    Iso.refl_hom, Iso.symm_hom, mapIso_hom, triangleCategory_comp, Iso.trans_inv, mapIso_inv,
      Triangle.isoMk_inv,
    Iso.refl_inv, Iso.symm_inv, TriangleMorphism.comp_hom₁, Triangle.mk_obj₁,
      Triangle.homMk_hom₁, mapTriangle_map_hom₁,
    map_id, Category.id_comp, ShortComplex.ShortExact.singleTrianglePlusMap_hom₁]
  erw [(derivedPushforwardPlus (relativeSecond R)).map_id,
    Category.id_comp, Category.id_comp, Category.comp_id]

@[simp] theorem diagonalCoefficientTensorTriangleMap_hom₂
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    (diagonalCoefficientTensorTriangleMap R f).hom₂ =
      (derivedPushforwardPlus (relativeSecond R)).map
        ((DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).map
          (diagonalBundleTensorSequenceMap R f).τ₂) := by
  simp only [diagonalCoefficientTensorTriangleMap, mapTriangle_obj, diagonalCoefficientToRawIso,
    diagonalCoefficientTensorTriangleIso, diagonalDerivedTensorTrianglePlusIso, Iso.trans_hom,
      Triangle.isoMk_hom,
    Iso.refl_hom, Iso.symm_hom, mapIso_hom, triangleCategory_comp, Iso.trans_inv, mapIso_inv,
      Triangle.isoMk_inv,
    Iso.refl_inv, Iso.symm_inv, TriangleMorphism.comp_hom₂, Triangle.mk_obj₂,
      Triangle.homMk_hom₂, mapTriangle_map_hom₂,
    map_id, Category.id_comp, ShortComplex.ShortExact.singleTrianglePlusMap_hom₂]
  erw [(derivedPushforwardPlus (relativeSecond R)).map_id,
    Category.id_comp, Category.id_comp, Category.comp_id]

/-- The third component is precisely tensoring the original coefficient map with Q. -/
@[simp] theorem diagonalCoefficientTensorTriangleMap_hom₃
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    (diagonalCoefficientTensorTriangleMap R f).hom₃ =
      (DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).map
        ((moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)).map f) := by
  have h := diagonalCoefficientVertexComparison_naturality R f
  have he : (diagonalCoefficientTensorTriangleMap R f).hom₃ =
      (diagonalCoefficientVertexComparison R E).inv ≫
        (derivedPushforwardPlus (relativeSecond R)).map
          ((DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).map
            (diagonalBundleTensorSequenceMap R f).τ₃) ≫
        (diagonalCoefficientVertexComparison R E').hom := by
    simp [diagonalCoefficientTensorTriangleMap, diagonalCoefficientToRawIso,
      diagonalCoefficientTensorTriangleIso, diagonalDerivedTensorTrianglePlusIso,
      diagonalCoefficientVertexComparison, Category.assoc]
  rw [he, h, Iso.inv_hom_id_assoc]

/-- The natural generation map retains the original map on all three coefficient vertices. -/
def diagonalGenerationTriangleMap
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    diagonalGenerationTriangle R E ⟶ diagonalGenerationTriangle R E' :=
  (diagonalGenerationTriangleIso R E).hom ≫ diagonalCoefficientTensorTriangleMap R f ≫
    (diagonalGenerationTriangleIso R E').inv

@[simp] theorem diagonalGenerationTriangleMap_hom₁
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    (diagonalGenerationTriangleMap R f).hom₁ = diagonalGenerationFirstMap R f := by
  dsimp only [diagonalGenerationTriangleMap, TriangleMorphism.comp_hom₁]
  change (diagonalGenerationFirstIso R E).hom ≫ _ ≫
    (diagonalGenerationFirstIso R E').inv = _
  rw [diagonalCoefficientTensorTriangleMap_hom₁,
    ← Category.assoc, ← diagonalGenerationFirstIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

@[simp] theorem diagonalGenerationTriangleMap_hom₂
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    (diagonalGenerationTriangleMap R f).hom₂ = diagonalGenerationSecondMap R f := by
  dsimp only [diagonalGenerationTriangleMap, TriangleMorphism.comp_hom₂]
  change (diagonalGenerationSecondIso R E).hom ≫ _ ≫
    (diagonalGenerationSecondIso R E').inv = _
  rw [diagonalCoefficientTensorTriangleMap_hom₂,
    ← Category.assoc, ← diagonalGenerationSecondIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

@[simp] theorem diagonalGenerationTriangleMap_hom₃
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    (diagonalGenerationTriangleMap R f).hom₃ =
      (DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).map
        ((moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)).map f) := by
  simp only [diagonalGenerationTriangleMap, diagonalGenerationTriangleIso, Triangle.isoMk_hom,
    Iso.refl_hom,
    Triangle.isoMk_inv, Iso.refl_inv, triangleCategory_comp, TriangleMorphism.comp_hom₃,
      Triangle.homMk_hom₃,
    diagonalCoefficientTensorTriangleMap_hom₃, Category.id_comp]
  exact Category.comp_id _

/-- Original identity arrows give the identity generation triangle map. -/
theorem diagonalGenerationTriangleMap_id (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    diagonalGenerationTriangleMap R (𝟙 E) = 𝟙 (diagonalGenerationTriangle R E) := by
  ext : 1 <;> simp [diagonalGenerationFirstMap, diagonalGenerationSecondMap] <;> rfl

/-- Original composition is retained, including the connecting-morphism square. -/
theorem diagonalGenerationTriangleMap_comp
    {E E' E'' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] [IsFiniteLocallyFree (twoChartLine R) E'']
    (f : E ⟶ E') (g : E' ⟶ E'') :
    diagonalGenerationTriangleMap R (f ≫ g) =
      diagonalGenerationTriangleMap R f ≫ diagonalGenerationTriangleMap R g := by
  ext : 1 <;> simp [diagonalGenerationFirstMap, diagonalGenerationSecondMap]

end Quillen.Scheme.ProjectiveLine
