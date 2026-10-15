/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalCoefficientFunctors
public import Quillen.Algebra.Homology.DerivedCategory.PlusComplexTriangle
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Quillen.Algebra.Homology.CochainComplexPlusNatTrans

/-! # Functorial original all-coefficient diagonal complex triangle

For actual bounded-below complexes, the original sheafified diagonal sequence is
short exact in every degree. Its canonical D+ triangle retains the literal first
pullback, tensor incidence, adjoint quotient, and Mathlib cone connecting sign.
Exactness of all three coefficient functors makes the entire triangle functor
invert every quasi-isomorphism and descend through the genuine D+ localization.
-/

@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules

local instance diagonalComplexStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable (R : CommRingCat.{u})
/-- The literal termwise original diagonal tensor sequence of bounded-below complexes. -/
def diagonalComplexSequenceFunctor :
    CochainComplex.Plus (twoChartLine R).Modules ⥤
      ShortComplex (CochainComplex.Plus (relativeSquare R).Modules) where
  obj K := ShortComplex.mk
    ((diagonalCoefficientMap R (diagonalIncidence R)).mapCochainComplexPlus.app K)
    ((diagonalCoefficientMap R (diagonalQuotientMap R)).mapCochainComplexPlus.app K) (by
      apply ObjectProperty.hom_ext
      ext n : 1
      change (moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeFirst R)).obj (K.obj.X n))).map
          (diagonalIncidence R) ≫
        (moduleTensorLeftFunctor (relativeSquare R)
          ((Scheme.Modules.pullback (relativeFirst R)).obj (K.obj.X n))).map
            (diagonalQuotientMap R) = 0
      rw [← CategoryTheory.Functor.map_comp, diagonalIncidence_quotient,
        CategoryTheory.Functor.map_zero])
  map f := ShortComplex.homMk
    ((diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₁).mapCochainComplexPlus.map f)
    ((diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₂).mapCochainComplexPlus.map f)
    ((diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₃).mapCochainComplexPlus.map f)
    ((diagonalCoefficientMap R (diagonalIncidence R)).mapCochainComplexPlus.naturality f)
    ((diagonalCoefficientMap R (diagonalQuotientMap R)).mapCochainComplexPlus.naturality f)
  map_id K := by
    apply ShortComplex.hom_ext
    · exact (diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₁).mapCochainComplexPlus.map_id K
    · exact (diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₂).mapCochainComplexPlus.map_id K
    · exact (diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₃).mapCochainComplexPlus.map_id K
  map_comp f g := by
    apply ShortComplex.hom_ext
    · exact (diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₁).mapCochainComplexPlus.map_comp f g
    · exact (diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₂).mapCochainComplexPlus.map_comp f g
    · exact (diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₃).mapCochainComplexPlus.map_comp f g

/-- Degree evaluation recovers the literal accepted original all-coefficient sheaf sequence. -/
theorem diagonalComplexSequence_degree
    (K : CochainComplex.Plus (twoChartLine R).Modules) (n : ℤ) :
    (((diagonalComplexSequenceFunctor R).obj K).map
      (CochainComplex.Plus.ι (relativeSquare R).Modules)).map
        (HomologicalComplex.eval (relativeSquare R).Modules (.up ℤ) n) =
      diagonalBundleTensorSequence R (K.obj.X n) := rfl

/-- Termwise accepted exactness gives an actual short exact sequence of complexes. -/
theorem diagonalComplexSequence_shortExact
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (((diagonalComplexSequenceFunctor R).obj K).map
      (CochainComplex.Plus.ι (relativeSquare R).Modules)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  rw [diagonalComplexSequence_degree]
  exact diagonalBundleTensorSequence_shortExact_all R (K.obj.X n)

/-- The actual original complex triangle, with all three coefficient chain maps. -/
def diagonalComplexTensorTriangleFunctor :
    CochainComplex.Plus (twoChartLine R).Modules ⥤
      Triangle (DerivedCategory.Plus (relativeSquare R).Modules) where
  obj K := DerivedCategory.Plus.triangleOfSESPlus (diagonalComplexSequence_shortExact R K)
  map f := DerivedCategory.Plus.triangleOfSESPlusMap
    (diagonalComplexSequence_shortExact R _) (diagonalComplexSequence_shortExact R _)
    ((diagonalComplexSequenceFunctor R).map f)
  map_id K := by
    ext : 1 <;> simp only [DerivedCategory.Plus.triangleOfSESPlusMap_hom₁,
      DerivedCategory.Plus.triangleOfSESPlusMap_hom₂,
      DerivedCategory.Plus.triangleOfSESPlusMap_hom₃]
    all_goals simp [diagonalComplexSequenceFunctor, DerivedCategory.Plus.triangleOfSESPlus]
  map_comp f g := by
    ext : 1 <;> simp only [DerivedCategory.Plus.triangleOfSESPlusMap_hom₁,
      DerivedCategory.Plus.triangleOfSESPlusMap_hom₂,
      DerivedCategory.Plus.triangleOfSESPlusMap_hom₃]
    all_goals simp [diagonalComplexSequenceFunctor]

/-- The actual original all-coefficient complex triangle is distinguished in D+. -/
theorem diagonalComplexTensorTriangle_distinguished
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (diagonalComplexTensorTriangleFunctor R).obj K ∈
      distTriang (DerivedCategory.Plus (relativeSquare R).Modules) :=
  DerivedCategory.Plus.triangleOfSESPlus_distinguished (diagonalComplexSequence_shortExact R K)

/-- The original first coefficient chain map is retained. -/
@[simp] theorem diagonalComplexTensorTriangleMap_hom₁
    {K L : CochainComplex.Plus (twoChartLine R).Modules} (f : K ⟶ L) :
    ((diagonalComplexTensorTriangleFunctor R).map f).hom₁ =
      DerivedCategory.Plus.Q.map
        ((diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₁).mapCochainComplexPlus.map f) :=
  DerivedCategory.Plus.triangleOfSESPlusMap_hom₁ _ _ _
/-- The original second coefficient chain map is retained. -/
@[simp] theorem diagonalComplexTensorTriangleMap_hom₂
    {K L : CochainComplex.Plus (twoChartLine R).Modules} (f : K ⟶ L) :
    ((diagonalComplexTensorTriangleFunctor R).map f).hom₂ =
      DerivedCategory.Plus.Q.map
        ((diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₂).mapCochainComplexPlus.map f) :=
  DerivedCategory.Plus.triangleOfSESPlusMap_hom₂ _ _ _
/-- The original third coefficient chain map is retained. -/
@[simp] theorem diagonalComplexTensorTriangleMap_hom₃
    {K L : CochainComplex.Plus (twoChartLine R).Modules} (f : K ⟶ L) :
    ((diagonalComplexTensorTriangleFunctor R).map f).hom₃ =
      DerivedCategory.Plus.Q.map
        ((diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₃).mapCochainComplexPlus.map f) :=
  DerivedCategory.Plus.triangleOfSESPlusMap_hom₃ _ _ _

/-- The first arrow is literally the original tensor incidence chain map. -/
theorem diagonalComplexTensorTriangle_mor₁
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    ((diagonalComplexTensorTriangleFunctor R).obj K).mor₁ =
      DerivedCategory.Plus.Q.map
        ((diagonalCoefficientMap R (diagonalIncidence R)).mapCochainComplexPlus.app K) := rfl

/-- The second arrow is literally the original tensor adjoint quotient chain map. -/
theorem diagonalComplexTensorTriangle_mor₂
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    ((diagonalComplexTensorTriangleFunctor R).obj K).mor₂ =
      DerivedCategory.Plus.Q.map
        ((diagonalCoefficientMap R (diagonalQuotientMap R)).mapCochainComplexPlus.app K) := rfl

/-- The connecting arrow uses precisely the original canonical cone sign and inclusion shift. -/
theorem diagonalComplexTensorTriangle_mor₃
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    ((diagonalComplexTensorTriangleFunctor R).obj K).mor₃ =
      DerivedCategory.Plus.ι.preimage
        (DerivedCategory.triangleOfSESδ (diagonalComplexSequence_shortExact R K) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
            (DerivedCategory.Plus.Q.obj
              ((diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₁).mapCochainComplexPlus.obj K))) := rfl

/-- Exactness of a coefficient functor turns genuine quasi-isomorphisms into D+ isomorphisms. -/
theorem diagonalCoefficientMap_isIso_of_quasiIso
    (A : (relativeSquare R).Modules) [(diagonalCoefficientFunctor R A).PreservesHomology]
    {K L : CochainComplex.Plus (twoChartLine R).Modules} (f : K ⟶ L)
    (hf : CochainComplex.Plus.quasiIso (twoChartLine R).Modules f) :
    IsIso (DerivedCategory.Plus.Q.map
      ((diagonalCoefficientFunctor R A).mapCochainComplexPlus.map f)) := by
  let : QuasiIso f.hom := hf
  apply Localization.inverts DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (relativeSquare R).Modules)
  change QuasiIso
    (((diagonalCoefficientFunctor R A).mapHomologicalComplex (.up ℤ)).map f.hom)
  infer_instance

/-- The whole original triangle functor inverts genuine coefficient quasi-isomorphisms. -/
theorem diagonalComplexTensorTriangle_inverts :
    (CochainComplex.Plus.quasiIso (twoChartLine R).Modules).IsInvertedBy
      (diagonalComplexTensorTriangleFunctor R) := by
  intro K L f hf
  apply Triangle.isIso_of_isIsos
  · rw [diagonalComplexTensorTriangleMap_hom₁]
    exact diagonalCoefficientMap_isIso_of_quasiIso R _ f hf
  · rw [diagonalComplexTensorTriangleMap_hom₂]
    exact diagonalCoefficientMap_isIso_of_quasiIso R _ f hf
  · rw [diagonalComplexTensorTriangleMap_hom₃]
    exact diagonalCoefficientMap_isIso_of_quasiIso R _ f hf

/-- The genuine D+ localization of the entire original all-coefficient triangle functor. -/
def diagonalDerivedComplexTriangleFunctor :
    DerivedCategory.Plus (twoChartLine R).Modules ⥤
      Triangle (DerivedCategory.Plus (relativeSquare R).Modules) :=
  Localization.lift (diagonalComplexTensorTriangleFunctor R)
    (diagonalComplexTensorTriangle_inverts R) DerivedCategory.Plus.Q

/-- The canonical factorization identifies every localized complex
with its actual original triangle. -/
def diagonalDerivedComplexTriangleFactors :
    DerivedCategory.Plus.Q ⋙ diagonalDerivedComplexTriangleFunctor R ≅
      diagonalComplexTensorTriangleFunctor R :=
  Localization.fac _ (diagonalComplexTensorTriangle_inverts R) _

/-- Naturality retains the original coefficient chain map under the localization factorization. -/
@[reassoc] theorem diagonalDerivedComplexTriangleFactors_naturality
    {K L : CochainComplex.Plus (twoChartLine R).Modules} (f : K ⟶ L) :
    (diagonalDerivedComplexTriangleFunctor R).map (DerivedCategory.Plus.Q.map f) ≫
      (diagonalDerivedComplexTriangleFactors R).hom.app L =
    (diagonalDerivedComplexTriangleFactors R).hom.app K ≫
      (diagonalComplexTensorTriangleFunctor R).map f :=
  (diagonalDerivedComplexTriangleFactors R).hom.naturality f

/-- On a genuine localization roof, the descended map is the inverse original
triangle map followed by the original forward triangle map, under the canonical factors. -/
theorem diagonalDerivedComplexTriangle_roof
    {K L M : CochainComplex.Plus (twoChartLine R).Modules} (s : M ⟶ K) (f : M ⟶ L)
    (hs : CochainComplex.Plus.quasiIso (twoChartLine R).Modules s) :
    letI : IsIso (DerivedCategory.Plus.Q.map s) :=
      Localization.inverts DerivedCategory.Plus.Q
        (CochainComplex.Plus.quasiIso (twoChartLine R).Modules) s hs
    letI : IsIso ((diagonalComplexTensorTriangleFunctor R).map s) :=
      diagonalComplexTensorTriangle_inverts R s hs
    (diagonalDerivedComplexTriangleFunctor R).map
      (inv (DerivedCategory.Plus.Q.map s) ≫ DerivedCategory.Plus.Q.map f) ≫
        (diagonalDerivedComplexTriangleFactors R).hom.app L =
      (diagonalDerivedComplexTriangleFactors R).hom.app K ≫
        inv ((diagonalComplexTensorTriangleFunctor R).map s) ≫
          (diagonalComplexTensorTriangleFunctor R).map f := by
  let : IsIso (DerivedCategory.Plus.Q.map s) :=
    Localization.inverts DerivedCategory.Plus.Q
      (CochainComplex.Plus.quasiIso (twoChartLine R).Modules) s hs
  let : IsIso ((diagonalComplexTensorTriangleFunctor R).map s) :=
    diagonalComplexTensorTriangle_inverts R s hs
  have hn := diagonalDerivedComplexTriangleFactors_naturality R s
  have hi : (diagonalDerivedComplexTriangleFunctor R).map
      (inv (DerivedCategory.Plus.Q.map s)) ≫
        (diagonalDerivedComplexTriangleFactors R).hom.app M =
      (diagonalDerivedComplexTriangleFactors R).hom.app K ≫
        inv ((diagonalComplexTensorTriangleFunctor R).map s) := by
    rw [CategoryTheory.Functor.map_inv]
    apply (cancel_mono ((diagonalComplexTensorTriangleFunctor R).map s)).mp
    rw [Category.assoc, ← hn, IsIso.inv_hom_id_assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    diagonalDerivedComplexTriangleFactors_naturality, ← Category.assoc, hi, Category.assoc]

/-- The canonical connecting square holds for every genuine derived morphism. -/
theorem diagonalDerivedComplexTriangle_connecting_naturality
    {K L : DerivedCategory.Plus (twoChartLine R).Modules} (f : K ⟶ L) :
    ((diagonalDerivedComplexTriangleFunctor R).obj K).mor₃ ≫
      (((diagonalDerivedComplexTriangleFunctor R).map f).hom₁)⟦1⟧' =
    ((diagonalDerivedComplexTriangleFunctor R).map f).hom₃ ≫
      ((diagonalDerivedComplexTriangleFunctor R).obj L).mor₃ :=
  ((diagonalDerivedComplexTriangleFunctor R).map f).comm₃

/-- Every intrinsic bounded-below derived input carries a distinguished original triangle. -/
theorem diagonalDerivedComplexTriangle_distinguished
    (K : DerivedCategory.Plus (twoChartLine R).Modules) :
    (diagonalDerivedComplexTriangleFunctor R).obj K ∈
      distTriang (DerivedCategory.Plus (relativeSquare R).Modules) := by
  let := Localization.essSurj DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (twoChartLine R).Modules)
  let L := DerivedCategory.Plus.Q.objPreimage K
  let e := (diagonalDerivedComplexTriangleFunctor R).mapIso
    (DerivedCategory.Plus.Q.objObjPreimageIso K)
  exact isomorphic_distinguished _ (diagonalComplexTensorTriangle_distinguished R L) _
    (e.symm ≪≫ (diagonalDerivedComplexTriangleFactors R).app L)
end AlgebraicGeometry.Scheme.ProjectiveLine
