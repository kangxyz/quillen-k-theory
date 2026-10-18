/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.DoubleLaurentInclusion

/-!
# Regression for the original double Laurent face

The two accepted face formulas give an exact comparison after the original
swap on the input loop. The swap's involution checks its contravariant direction;
no equality between the full cone comparisons is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.KTheory.Bass Quillen.KTheory.Bass.DoubleLaurentInclusion
universe u w
namespace QuillenTest.DoubleLaurentComparison

/-- The original contravariant swap is its own inverse on the actual double product. -/
theorem original_swap_involutive (X : Scheme.{u}ᵒᵖ) :
    doubleLaurentSwap X ≫ doubleLaurentSwap X = 𝟙 _ := by
  apply Quiver.Hom.unop_inj
  exact baseProductSwapMap_comp (laurentProjection (.of (ULift.{u} ℤ)))
    (laurentProjection (.of (ULift.{u} ℤ))) X.unop

/-- On the double Laurent face the difference is exactly the original input swap. -/
theorem double_face_comparison (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) :
    parameterLoopingMap (laurentInclusion F (laurent.op.obj X)) ≫
        laurentInclusion ((strictDiagramFunctor squareFunctor).obj F) X ≫
        (GeometricSeedCospan.chiGeom F).app X =
      parameterLoopingMap (F.map (doubleLaurentSwap X)) ≫
        parameterLoopingMap (laurentInclusion F (laurent.op.obj X)) ≫
        laurentInclusion ((strictDiagramFunctor squareFunctor).obj F) X ≫
        LoopFactor.coneStrength
          ((geometricCone F).mapArrow.mapArrow.obj (square X)) := by
  rw [geometric_doubleLaurent, looping_doubleLaurent]
  exact parameterLoopingFunctor.map_comp _ _

#print axioms chiGeom_laurentInclusion
#print axioms geometric_doubleLaurent
#print axioms looping_doubleLaurent
#print axioms geometric_doubleLaurent_apply
#print axioms looping_doubleLaurent_apply
#print axioms original_swap_involutive
#print axioms double_face_comparison

end QuillenTest.DoubleLaurentComparison
