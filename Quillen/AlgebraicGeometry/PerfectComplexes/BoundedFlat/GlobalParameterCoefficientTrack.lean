/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentTrack

/-! # Every original Laurent-track time under integral Spec restriction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open GlobalSectionChangeIndex ParameterLaurentUnit GeometricSeedCospan

/-- The actual global Model maps satisfy the complete coefficient square strictly. -/
theorem model_coefficient_square
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterModels.ambient Q.left).map (coefficient.app (specUnder.obj a)) ≫
        globalModel.map (laurentParameterIso Q a).hom.op =
      globalModel.map (canonicalRowIso Q a).hom.op ≫
        (globalRow Q).map ((laurentUnderCoefficient _).app a) := by
  change globalModel.map
      ((baseProductFunctor (toIntegerBase Q.left)).map
        ((baseProductProjection
          (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
            (CommRingCat.of (ULift.{u} ℤ)))).app
          (Spec a.right))).op ≫ globalModel.map (laurentParameterIso Q a).hom.op =
    globalModel.map (canonicalRowIso Q a).hom.op ≫
      globalModel.map (AlgebraicGeometry.Scheme.BaseChange.Coefficients.laurentProjection Q a).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  rw [laurentParameterIso_coefficient]

/-- Spec restriction preserves the actual scalar realization at every native degree and time. -/
theorem track_square
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterModels.ambient Q.left).obj (specUnder.obj a))).space n) :
    (prespectrumMap (globalModel.map (laurentParameterIso Q a).hom.op)).map n
        (((ParameterLaurentTrack.ambientTrack Q.left).homotopy (specUnder.obj a)).level n (r,x)) =
      (((globalLaurentAction Q).track.homotopy a).level n
        (r, (prespectrumMap (globalModel.map (canonicalRowIso Q a).hom.op)).map n x)) := by
  have h := model_coefficient_square Q a
  exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
    (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg Model.Hom.functor h))
      (ambientUnit Q.left (specUnder.obj a)) (globalLaurentUnit Q a)
      (ambientUnit_preserves Q a).whisker) n r x

end Quillen.PerfectComplexes.GlobalParameterCoefficient
