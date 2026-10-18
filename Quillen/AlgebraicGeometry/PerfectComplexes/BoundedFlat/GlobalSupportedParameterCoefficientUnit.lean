/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterCoefficientModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedForgetSeed

/-!
# The original supported Laurent unit under the integral Spec comparison

The complete Laurent comparison is the actual supported parameter reindexing followed by
its original coefficient-row isomorphism. Its strict forgetful square transfers preservation
of the original ambient scalar through the faithful supported inclusion. Both support
predicates and the specified lifted units are unchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex ParameterLaurentUnit ParameterLaurentTrack
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The actual supported Laurent corner of the complete Spec-row comparison. -/
def laurentModelMap (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterModels.supported f.left).obj (GlobalIndex.laurent.op.obj (specUnder.obj a)) ⟶
      (supportedRow f).obj ((laurentUnderFunctor _).obj a) :=
  (ParameterModels.supported f.left).map (laurentSpecIso a.right).hom.op ≫
    (parameterSupportedRowIso f).hom.app ((laurentUnderFunctor _).obj a)

/-- Forgetting support gives the entire original ambient Laurent comparison. -/
theorem laurentModelMap_forget (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    laurentModelMap f a ≫ (supportedRowForget f).app ((laurentUnderFunctor _).obj a) =
      (ParameterModels.forget f.left).app (GlobalIndex.laurent.op.obj (specUnder.obj a)) ≫
        globalModel.map (laurentParameterIso Q a).hom.op := by
  have hrow := NatTrans.congr_app (parameterSupportedRowIso_forget f)
    ((laurentUnderFunctor _).obj a)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hrow
  rw [laurentModelMap, Category.assoc, hrow, parameterRowModelIso_hom_app,
    ← Category.assoc]
  erw [(ParameterModels.forget f.left).naturality (laurentSpecIso a.right).hom.op]
  rw [Category.assoc]
  congr 1

/-- The faithful original support inclusion detects preservation of the same Laurent unit. -/
theorem supportedUnit_preserves (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (laurentModelMap f a).functor
      (supportedUnit f.left (specUnder.obj a)) (supportedLaurentUnit f a) := by
  let : (rowSupported f ((laurentUnderFunctor _).obj a)).ι.Faithful :=
    (rowSupported f ((laurentUnderFunctor _).obj a)).fullyFaithfulι.faithful
  have h := congrArg Model.Hom.functor (laurentModelMap_forget f a)
  apply evaluationPreserves_of_eq (laurentModelMap f a).functor
    (rowSupported f ((laurentUnderFunctor _).obj a)).ι
    ((parameterSupported f.left (GlobalIndex.laurent.op.obj (specUnder.obj a))).ι ⋙
      (globalModel.map (laurentParameterIso Q a).hom.op).functor) h
    (supportedUnit f.left (specUnder.obj a)) (supportedLaurentUnit f a)
    (globalLaurentUnit Q a)
  · intro x
    change (globalModel.map (laurentParameterIso Q a).hom.op).functor.map
      (((supportedUnit f.left (specUnder.obj a)).hom.app x).hom) = _
    rw [show ((supportedUnit f.left (specUnder.obj a)).hom.app x).hom =
      (ambientUnit Q.left (specUnder.obj a)).hom.app x.obj from
        forget_unit f.left (specUnder.obj a) x]
    exact GlobalParameterCoefficient.ambientUnit_preserves Q a x.obj
  · exact supportedRowForget_unit f a

end Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
