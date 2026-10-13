/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.TensorExact
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalCokernel
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The tensor triangle of the original twisted diagonal sequence

For a vector bundle on the affine base, tensor the proved original diagonal
sequence by its literal pullback along the first projection followed by the
structure morphism. The result is short exact and gives the actual distinguished
triangle in the standard derived category, naturally in the original coefficient
arrows. Both triangle arrows retain the original incidence and adjoint quotient.

This scope concerns coefficients pulled back from the affine base. Tensoring with
arbitrary projective-line bundles, projection formulas, and generation are separate
comparisons and are not asserted here.
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
local instance diagonalTensorStandardDerived (R : CommRingCat.{u}) :
    HasDerivedCategory.{u + 1} (relativeSquare R).Modules :=
  HasDerivedCategory.standard _

/-- The original twisted diagonal sequence tensored with a coefficient pulled back from the base. -/
def diagonalTensorSequence (R : CommRingCat.{u}) (M : (Spec R).Modules) :
    ShortComplex (relativeSquare R).Modules :=
  (diagonalIncidenceSequence R).map (moduleTensorLeftFunctor (relativeSquare R)
    ((Scheme.Modules.pullback (relativeFirst R ≫ projection R)).obj M))

/-- An original base coefficient arrow induces the actual tensor map of diagonal sequences. -/
def diagonalTensorSequenceMap (R : CommRingCat.{u}) {M N : (Spec R).Modules}
    (f : M ⟶ N) : diagonalTensorSequence R M ⟶ diagonalTensorSequence R N :=
  (diagonalIncidenceSequence R).mapNatTrans (moduleTensorCoefficientMap (relativeSquare R)
    ((Scheme.Modules.pullback (relativeFirst R ≫ projection R)).map f))

/-- The actual tensor sequence is short exact for any affine-base vector bundle. -/
theorem diagonalTensorSequence_shortExact (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] : (diagonalTensorSequence R M).ShortExact :=
  tensor_shortExact_pullback_affine_vectorBundle R (relativeFirst R ≫ projection R)
    M (diagonalIncidenceSequence R) (diagonalIncidenceSequence_shortExact R)

/-- The actual derived triangle of the tensored original twisted diagonal sequence. -/
def diagonalTensorTriangle (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] : Triangle (DerivedCategory (relativeSquare R).Modules) :=
  (diagonalTensorSequence_shortExact R M).singleTriangle

/-- The derived triangle map induced by an original affine-base coefficient arrow. -/
def diagonalTensorTriangleMap (R : CommRingCat.{u}) {M N : (Spec R).Modules}
    [IsFiniteLocallyFree (Spec R) M] [IsFiniteLocallyFree (Spec R) N] (f : M ⟶ N) :
    diagonalTensorTriangle R M ⟶ diagonalTensorTriangle R N :=
  ShortComplex.ShortExact.singleTriangle.map (diagonalTensorSequence_shortExact R M)
    (diagonalTensorSequence_shortExact R N) (diagonalTensorSequenceMap R f)

/-- The triangle map of the original identity coefficient arrow is the identity. -/
theorem diagonalTensorTriangleMap_id (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] :
    diagonalTensorTriangleMap R (𝟙 M) = 𝟙 (diagonalTensorTriangle R M) := by
  let P := Scheme.Modules.pullback (relativeFirst R ≫ projection R)
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
theorem diagonalTensorTriangleMap_comp (R : CommRingCat.{u})
    {M N P : (Spec R).Modules} [IsFiniteLocallyFree (Spec R) M]
    [IsFiniteLocallyFree (Spec R) N] [IsFiniteLocallyFree (Spec R) P]
    (f : M ⟶ N) (g : N ⟶ P) :
    diagonalTensorTriangleMap R (f ≫ g) =
      diagonalTensorTriangleMap R f ≫ diagonalTensorTriangleMap R g := by
  ext : 1 <;>
    simp [diagonalTensorTriangleMap, ShortComplex.ShortExact.singleTriangle.map,
      diagonalTensorSequenceMap, moduleTensorCoefficientMap_comp]

/-- The triangle with the original tensor incidence and quotient arrows is distinguished. -/
theorem diagonalTensorTriangle_distinguished (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] :
    diagonalTensorTriangle R M ∈ distTriang (DerivedCategory (relativeSquare R).Modules) :=
  (diagonalTensorSequence_shortExact R M).singleTriangle_distinguished

/-- Its first arrow is the actual tensor image of the original incidence, placed in degree zero. -/
theorem diagonalTensorTriangle_mor₁ (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] :
    (diagonalTensorTriangle R M).mor₁ = (singleFunctor (relativeSquare R).Modules 0).map
      ((moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeFirst R ≫ projection R)).obj M)).map
        (diagonalIncidence R)) := rfl

/-- Its second arrow is the actual tensor image of the original adjoint quotient arrow. -/
theorem diagonalTensorTriangle_mor₂ (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] :
    (diagonalTensorTriangle R M).mor₂ = (singleFunctor (relativeSquare R).Modules 0).map
      ((moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeFirst R ≫ projection R)).obj M)).map
        (diagonalQuotientMap R)) := rfl

end Quillen.Scheme.ProjectiveLine
