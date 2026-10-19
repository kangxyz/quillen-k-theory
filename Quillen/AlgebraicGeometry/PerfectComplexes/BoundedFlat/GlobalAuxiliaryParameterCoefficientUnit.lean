/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionRestrictionUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentTrack
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportedUnits

/-! # The actual forward Laurent unit on auxiliary-supported integral comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex ParameterLaurentUnit ParameterLaurentTrack

/-- The actual Laurent comparison followed by original coefficient restriction. -/
def nativeLaurentMap (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  globalModel.map (laurentParameterIso Q a).hom.op ≫
    (rowRestriction Q).app ((laurentUnderFunctor _).obj a)

/-- This whole original Model map preserves the original forward coefficient Laurent unit. -/
theorem nativeLaurentMap_unit (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (nativeLaurentMap Q a).functor
      (ambientUnit Q.left (specUnder.obj a)) (boundedFlatCoefficientSectionLaurentUnitIso Q a) := by
  intro x
  change ((rowRestriction Q).app ((laurentUnderFunctor _).obj a)).functor.map
      ((globalModel.map (laurentParameterIso Q a).hom.op).functor.map
        ((ambientUnit Q.left (specUnder.obj a)).hom.app x)) = _
  rw [GlobalParameterCoefficient.ambientUnit_preserves Q a x]
  exact coefficientRestriction_unit_preserves _ (op Q, (laurentUnderFunctor _).obj a)
    (boundedFlatCoefficientUnit (op Q, (laurentUnderFunctor _).obj a)
      (laurentGlobalUnit a.right)) _

/-- A proved complete support-forget square transports the actual forward Laurent action. -/
theorem supportedLaurentMap_unit
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (U : (space (op Q, (laurentUnderFunctor _).obj a)).Opens)
    (m : (ParameterModels.supported T.ι).obj
        (GlobalIndex.laurent.op.obj (specUnder.obj a)) ⟶
      boundedFlatCoefficientSupportedSectionModel
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι)
    (h : m.functor ⋙ (boundedFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι =
      ((ParameterModels.forget T.ι).app
        (GlobalIndex.laurent.op.obj (specUnder.obj a))).functor ⋙
          (nativeLaurentMap Q a).functor) :
    Preserves m.functor (supportedUnit T.ι (specUnder.obj a))
      (boundedFlatCoefficientSupportSectionUnitIso
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι (laurentGlobalUnit a.right)) := by
  let : (boundedFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι.Faithful :=
    (boundedFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).fullyFaithfulι.faithful
  apply evaluationPreserves_of_eq m.functor
    (boundedFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι _ h
    (supportedUnit T.ι (specUnder.obj a)) _ (boundedFlatCoefficientSectionLaurentUnitIso Q a)
  · intro x
    change (nativeLaurentMap Q a).functor.map
      (((supportedUnit T.ι (specUnder.obj a)).hom.app x).hom) = _
    rw [show ((supportedUnit T.ι (specUnder.obj a)).hom.app x).hom =
      (ambientUnit Q.left (specUnder.obj a)).hom.app x.obj from
        forget_unit T.ι (specUnder.obj a) x]
    exact nativeLaurentMap_unit Q a x.obj
  · intro x
    exact boundedFlatCoefficientSupportSectionUnitIso_hom
      (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι (laurentGlobalUnit a.right) x

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
