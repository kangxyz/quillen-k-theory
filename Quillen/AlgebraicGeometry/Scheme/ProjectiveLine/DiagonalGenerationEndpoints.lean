/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PullbackSingleNaturality
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.SingleComparison
public import Aglib.AlgebraicGeometry.Modules.Tensor.Symmetry
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalProjectedTensorTriangle
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DerivedFlatBaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.PullbackTensorCompatibility
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.LineTensorCompatibility
public import Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.Basic

/-!
# Natural endpoints of the actual diagonal generation triangle

Identify the first two vertices of the original diagonal tensor triangle for finite
locally free coefficients on the two-chart projective line. The transported arrows
and distinguishedness retain the original incidence and connecting morphisms.

The base ring is arbitrary, including the zero ring. These interfaces preserve
the accepted vector-bundle scope; they do not establish a projective-bundle
equivalence or a full coefficient extension.
-/

@[expose] public section

open CategoryTheory.Pretriangulated


open AlgebraicGeometry.Scheme.Modules

open Quillen




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry DerivedCategory
  CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme.Modules
/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance generationStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance generationStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The self-base-change identification is natural in the original QC sheaf maps. -/
theorem derivedSelfBaseChangeSingleIso_naturality (R : CommRingCat.{u})
    {M N : (twoChartLine R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (g : M ⟶ N) :
    (derivedFlatPullbackPlus (projection R)).map
        ((derivedPushforwardPlus (projection R)).map
          ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).map g)) ≫
      (derivedSelfBaseChangeSingleIso R N).hom =
    (derivedSelfBaseChangeSingleIso R M).hom ≫
      (derivedPushforwardPlus (relativeSecond R)).map
        ((DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).map
          ((Scheme.Modules.pullback (relativeFirst R)).map g)) := by
  dsimp only [derivedSelfBaseChangeSingleIso, derivedProjectionBaseChangeSingleIso,
    Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  erw [← Category.assoc, (derivedFlatBaseChangeMap (relativeFirst R) (relativeSecond R)
    (projection R) (projection R) (IsPullback.of_hasPullback _ _)).naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp, derivedFlatPullbackPlusSingleIso_naturality, Functor.map_comp]

/-- Right tensor with the actual tautological line preserves finite local freeness. -/
instance tautologicalRightTensor_finiteLocallyFree (R : CommRingCat.{u})
    (E : (twoChartLine R).Modules) [IsFiniteLocallyFree (twoChartLine R) E] :
    IsFiniteLocallyFree (twoChartLine R)
      ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalLine R)) := by
  apply finiteLocallyFree_of_affineCharts _
    (fun _ : Bool => CommRingCat.of (Polynomial R)) (polynomialChart R)
  · intro x
    obtain ⟨i, y, hy⟩ := polynomialChart_cover R x
    exact ⟨i, y, hy⟩
  · intro b
    let eL : (tautologicalLine R).restrict (polynomialChart R b) ≅
        SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf := by
      cases b
      · exact tautologicalLineMinusIso R
      · exact tautologicalLinePlusIso R
    let e := (tensorRestrictionIso (polynomialChart R b) E (tautologicalLine R)).symm ≪≫
      (moduleTensorLeftFunctor (Spec (.of (Polynomial R)))
        (E.restrict (polynomialChart R b))).mapIso eL ≪≫
      (SheafOfModulesOfCommRing.tensorRightUnitIso (Spec (.of (Polynomial R))).sheaf).app
        (E.restrict (polynomialChart R b))
    change ((moduleTensorLeftFunctor (twoChartLine R) E).obj
      (tautologicalLine R)).restrict (polynomialChart R b) ≅
        E.restrict (polynomialChart R b) at e
    exact finiteLocallyFree_of_iso e.symm

variable (R : CommRingCat.{u})

/-- The first intended generation vertex: the original p*Rp*(E tensor L). -/
def diagonalGenerationFirst (E : (twoChartLine R).Modules) :
    DerivedCategory.Plus (twoChartLine R).Modules :=
  (derivedFlatPullbackPlus (projection R)).obj
    ((derivedPushforwardPlus (projection R)).obj
      ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj
        ((moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R)).obj E)))

/-- The second intended generation vertex: the original Q tensor p*Rp*E. -/
def diagonalGenerationSecond (E : (twoChartLine R).Modules) :
    DerivedCategory.Plus (twoChartLine R).Modules :=
  (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine
    R)).rightDerivedFunctorPlus.obj
    ((derivedFlatPullbackPlus (projection R)).obj
      ((derivedPushforwardPlus (projection R)).obj
        ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj E)))

variable (E : (twoChartLine R).Modules) [IsFiniteLocallyFree (twoChartLine R) E]

/-- The first actual projected incidence vertex, identified by self base change and
by the accepted original pullback/tensor mate. -/
def diagonalGenerationFirstIso :
    diagonalGenerationFirst R E ≅ (diagonalCoefficientTensorTriangle R E).obj₁ :=
  derivedSelfBaseChangeSingleIso R
      ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalLine R)) ≪≫
    (derivedPushforwardPlus (relativeSecond R)).mapIso
      ((DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).mapIso
        (tautologicalPullbackTensorIso R (relativeFirst R) E))

/-- The projection-formula and single/tensor comparisons form a natural
identification before restricting to vector bundles. -/
def diagonalGenerationSecondTailIso :
    Scheme.Modules.pullback (relativeFirst R) ⋙
      DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0 ⋙
      derivedPushforwardPlus (relativeSecond R) ⋙
      (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine
        R)).rightDerivedFunctorPlus ≅
    Scheme.Modules.pullback (relativeFirst R) ⋙
      moduleTensorRightFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R)) ⋙
      DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0 ⋙
      derivedPushforwardPlus (relativeSecond R) :=
  isoWhiskerLeft (Scheme.Modules.pullback (relativeFirst R))
    (isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0)
      (derivedProjectionFormulaIso (relativeSecond R) (tautologicalQuotientLine R))) ≪≫
  isoWhiskerLeft (Scheme.Modules.pullback (relativeFirst R))
    (isoWhiskerRight (exactDerivedSingleNatIso (moduleTensorLeftFunctor (relativeSquare R)
      ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R))))
      (derivedPushforwardPlus (relativeSecond R))) ≪≫
  isoWhiskerLeft (Scheme.Modules.pullback (relativeFirst R))
    (isoWhiskerRight (moduleTensorSymmetryNatIso (relativeSquare R)
      ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R))).symm
      (DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0 ⋙
        derivedPushforwardPlus (relativeSecond R)))

/-- The second actual projected vertex, using the original projection formula,
its installed exact tensor unit, and the original sheafified braiding. -/
def diagonalGenerationSecondIso :
    diagonalGenerationSecond R E ≅ (diagonalCoefficientTensorTriangle R E).obj₂ :=
  (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine
    R)).rightDerivedFunctorPlus.mapIso
      (derivedSelfBaseChangeSingleIso R E) ≪≫
    (diagonalGenerationSecondTailIso R).app E

/-- The original maps between the first generation vertices. -/
def diagonalGenerationFirstMap {M N : (twoChartLine R).Modules} (f : M ⟶ N) :
    diagonalGenerationFirst R M ⟶ diagonalGenerationFirst R N :=
  (derivedFlatPullbackPlus (projection R)).map
    ((derivedPushforwardPlus (projection R)).map
      ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).map
        ((moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R)).map f)))

/-- The original maps between the second generation vertices. -/
def diagonalGenerationSecondMap {M N : (twoChartLine R).Modules} (f : M ⟶ N) :
    diagonalGenerationSecond R M ⟶ diagonalGenerationSecond R N :=
  (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine
    R)).rightDerivedFunctorPlus.map
    ((derivedFlatPullbackPlus (projection R)).map
      ((derivedPushforwardPlus (projection R)).map
        ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).map f)))

/-- Naturality of the first actual endpoint in every original coefficient arrow. -/
theorem diagonalGenerationFirstIso_naturality
    {M N : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) M]
    [IsFiniteLocallyFree (twoChartLine R) N] (f : M ⟶ N) :
    diagonalGenerationFirstMap R f ≫ (diagonalGenerationFirstIso R N).hom =
      (diagonalGenerationFirstIso R M).hom ≫
        (derivedPushforwardPlus (relativeSecond R)).map
          ((DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).map
            ((diagonalBundleTensorSequenceMap R f).τ₁)) := by
  let g : (moduleTensorLeftFunctor (twoChartLine R) M).obj (tautologicalLine R) ⟶
      (moduleTensorLeftFunctor (twoChartLine R) N).obj (tautologicalLine R) :=
    (moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R)).map f
  have hn := derivedSelfBaseChangeSingleIso_naturality R g
  have ht := (tautologicalPullbackTensorNatIso R (relativeFirst R)).hom.naturality f
  dsimp only [diagonalGenerationFirstMap, diagonalGenerationFirstIso, Iso.trans_hom,
    Functor.mapIso_hom]
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  erw [ht]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- Naturality of the second actual endpoint in every original coefficient arrow. -/
theorem diagonalGenerationSecondIso_naturality
    {M N : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) M]
    [IsFiniteLocallyFree (twoChartLine R) N] (f : M ⟶ N) :
    diagonalGenerationSecondMap R f ≫ (diagonalGenerationSecondIso R N).hom =
      (diagonalGenerationSecondIso R M).hom ≫
        (derivedPushforwardPlus (relativeSecond R)).map
          ((DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).map
            ((diagonalBundleTensorSequenceMap R f).τ₂)) := by
  have hn := derivedSelfBaseChangeSingleIso_naturality R f
  have ht := (diagonalGenerationSecondTailIso R).hom.naturality f
  dsimp only [diagonalGenerationSecondMap, diagonalGenerationSecondIso, Iso.trans_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, hn, Functor.map_comp, Category.assoc]
  erw [ht]
  simp only [Category.assoc]
  rfl

/-- The generation triangle has its actual coefficient vertex and retains the original
incidence, quotient and connecting maps under the specified endpoint comparisons. -/
def diagonalGenerationTriangle : Triangle (DerivedCategory.Plus (twoChartLine R).Modules) :=
  Triangle.mk
    ((diagonalGenerationFirstIso R E).hom ≫ (diagonalCoefficientTensorTriangle R E).mor₁ ≫
      (diagonalGenerationSecondIso R E).inv)
    ((diagonalGenerationSecondIso R E).hom ≫ (diagonalCoefficientTensorTriangle R E).mor₂)
    ((diagonalCoefficientTensorTriangle R E).mor₃ ≫
      (shiftFunctor _ (1 : ℤ)).map (diagonalGenerationFirstIso R E).inv)

/-- The explicit triangle comparison retains both original endpoint identifications. -/
def diagonalGenerationTriangleIso :
    diagonalGenerationTriangle R E ≅ diagonalCoefficientTensorTriangle R E := by
  refine Triangle.isoMk _ _ (diagonalGenerationFirstIso R E)
    (diagonalGenerationSecondIso R E) (Iso.refl _) ?_ ?_ ?_
  all_goals dsimp [diagonalGenerationTriangle]; simp

/-- This is the original distinguished incidence triangle, with both required
coefficient projection vertices identified over every commutative ring. -/
theorem diagonalGenerationTriangle_distinguished :
    diagonalGenerationTriangle R E ∈ distTriang (DerivedCategory.Plus (twoChartLine R).Modules) :=
  isomorphic_distinguished _ (diagonalCoefficientTensorTriangle_distinguished R E) _
    (diagonalGenerationTriangleIso R E)

end AlgebraicGeometry.Scheme.ProjectiveLine
