/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.TensorLocalExactness
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Pullback
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalCokernel
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The diagonal tensor triangle for arbitrary projective-line vector bundles

Tensor the original twisted diagonal sequence with the actual first-projection
pullback of any finite locally free sheaf on the original two-chart line.
Local tensor exactness supplies its standard derived distinguished triangle.
All incidence, quotient and coefficient-arrow maps remain the original ones.
No affine-base restriction on the coefficient is imposed. Diagonal tensor
identification, derived projection formulas and generation remain separate.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open DerivedCategory CategoryTheory.Pretriangulated
namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf

/-- The standard derived category of modules on the original relative square. -/
local instance diagonalBundleTensorStandardDerived (R : CommRingCat.{u}) :
    HasDerivedCategory.{u + 1} (relativeSquare R).Modules :=
  HasDerivedCategory.standard _

/-- The original twisted diagonal sequence tensored with
a coefficient pulled back from the first factor. -/
def diagonalBundleTensorSequence (R : CommRingCat.{u}) (M : (twoChartLine R).Modules) :
    ShortComplex (relativeSquare R).Modules :=
  (diagonalIncidenceSequence R).map (moduleTensorLeftFunctor (relativeSquare R)
    ((Scheme.Modules.pullback (relativeFirst R)).obj M))

/-- An original projective-line coefficient arrow induces
the actual tensor map of diagonal sequences. -/
def diagonalBundleTensorSequenceMap (R : CommRingCat.{u}) {M N : (twoChartLine R).Modules}
    (f : M ⟶ N) : diagonalBundleTensorSequence R M ⟶ diagonalBundleTensorSequence R N :=
  (diagonalIncidenceSequence R).mapNatTrans (moduleTensorCoefficientMap (relativeSquare R)
    ((Scheme.Modules.pullback (relativeFirst R)).map f))

/-- The actual tensor sequence is short exact for any vector bundle
on the original two-chart line. -/
theorem diagonalBundleTensorSequence_shortExact (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M] : (diagonalBundleTensorSequence R M).ShortExact :=
  tensor_shortExact_finiteLocallyFree
    ((Scheme.Modules.pullback (relativeFirst R)).obj M)
    (diagonalIncidenceSequence R) (diagonalIncidenceSequence_shortExact R)

/-- The actual derived triangle of the tensored original twisted diagonal sequence. -/
def diagonalBundleTensorTriangle (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M] :
    Triangle (DerivedCategory (relativeSquare R).Modules) :=
  (diagonalBundleTensorSequence_shortExact R M).singleTriangle

/-- The derived triangle map induced by an original projective-line coefficient arrow. -/
def diagonalBundleTensorTriangleMap (R : CommRingCat.{u}) {M N : (twoChartLine R).Modules}
    [IsFiniteLocallyFree (twoChartLine R) M] [IsFiniteLocallyFree (twoChartLine R) N] (f : M ⟶ N) :
    diagonalBundleTensorTriangle R M ⟶ diagonalBundleTensorTriangle R N :=
  ShortComplex.ShortExact.singleTriangle.map (diagonalBundleTensorSequence_shortExact R M)
    (diagonalBundleTensorSequence_shortExact R N) (diagonalBundleTensorSequenceMap R f)

/-- The triangle map of the original identity coefficient arrow is the identity. -/
theorem diagonalBundleTensorTriangleMap_id (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M] :
    diagonalBundleTensorTriangleMap R (𝟙 M) = 𝟙 (diagonalBundleTensorTriangle R M) := by
  let P := Scheme.Modules.pullback (relativeFirst R)
  let T := moduleTensorLeftFunctor (relativeSquare R) (P.obj M)
  have hT : moduleTensorCoefficientMap (relativeSquare R) (P.map (𝟙 M)) = 𝟙 T :=
    (congrArg (fun f => moduleTensorCoefficientMap (relativeSquare R) f)
      (P.map_id M)).trans (moduleTensorCoefficientMap_id _ _)
  have hA (A : (relativeSquare R).Modules) :
      (singleFunctor (relativeSquare R).Modules 0).map
        ((moduleTensorCoefficientMap (relativeSquare R) (P.map (𝟙 M))).app A) =
      𝟙 ((singleFunctor (relativeSquare R).Modules 0).obj (T.obj A)) := by
    have hApp : (moduleTensorCoefficientMap (relativeSquare R) (P.map (𝟙 M))).app A =
        𝟙 (T.obj A) := congrArg (fun α => α.app A) hT
    rw [hApp]
    exact (singleFunctor (relativeSquare R).Modules 0).map_id _
  ext : 1
  · exact hA (diagonalIncidenceSequence R).X₁
  · exact hA (diagonalIncidenceSequence R).X₂
  · exact hA (diagonalIncidenceSequence R).X₃

/-- Composition of original coefficient arrows is retained by the actual triangle maps. -/
theorem diagonalBundleTensorTriangleMap_comp (R : CommRingCat.{u})
    {M N P : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) M]
    [IsFiniteLocallyFree (twoChartLine R) N] [IsFiniteLocallyFree (twoChartLine R) P]
    (f : M ⟶ N) (g : N ⟶ P) :
    diagonalBundleTensorTriangleMap R (f ≫ g) =
      diagonalBundleTensorTriangleMap R f ≫ diagonalBundleTensorTriangleMap R g := by
  ext : 1 <;>
    simp [diagonalBundleTensorTriangleMap, ShortComplex.ShortExact.singleTriangle.map,
      diagonalBundleTensorSequenceMap, moduleTensorCoefficientMap_comp]

/-- The triangle with the original tensor incidence and quotient arrows is distinguished. -/
theorem diagonalBundleTensorTriangle_distinguished (R : CommRingCat.{u})
    (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M] :
    diagonalBundleTensorTriangle R M ∈ distTriang (DerivedCategory (relativeSquare R).Modules) :=
  (diagonalBundleTensorSequence_shortExact R M).singleTriangle_distinguished

/-- Its first arrow is the actual tensor image of the original incidence, placed in degree zero. -/
theorem diagonalBundleTensorTriangle_mor₁ (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M] :
    (diagonalBundleTensorTriangle R M).mor₁ = (singleFunctor (relativeSquare R).Modules 0).map
      ((moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeFirst R)).obj M)).map
        (diagonalIncidence R)) := rfl

/-- Its second arrow is the actual tensor image of the original adjoint quotient arrow. -/
theorem diagonalBundleTensorTriangle_mor₂ (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M] :
    (diagonalBundleTensorTriangle R M).mor₂ = (singleFunctor (relativeSquare R).Modules 0).map
      ((moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeFirst R)).obj M)).map
        (diagonalQuotientMap R)) := rfl

end Quillen.Scheme.ProjectiveLine
