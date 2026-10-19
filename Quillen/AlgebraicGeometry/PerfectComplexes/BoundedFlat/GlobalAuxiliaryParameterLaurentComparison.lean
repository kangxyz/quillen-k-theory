/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFiberBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenBassSeed

/-! # The three actual Laurent corners and their original forward units -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex ParameterLaurentTrack

/-- The actual affine Laurent comparison and row restriction form one complete Model map. -/
theorem nativeLaurentMap_factor
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterModels.ambient Q.left).map (laurentSpecIso a.right).hom.op ≫
      (parameterCoefficientRestriction Q).app ((laurentUnderFunctor _).obj a) =
        nativeLaurentMap Q a := by
  unfold parameterCoefficientRestriction
  rw [NatTrans.comp_app, parameterRowModelIso_hom_app]
  change globalModel.map _ ≫ globalModel.map _ ≫
    (rowRestriction Q).app ((laurentUnderFunctor _).obj a) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

/-- Any actual native support component with the full forget square retains its Laurent corner. -/
theorem laurentComponent_forget
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (U : (space (op Q, (laurentUnderFunctor _).obj a)).Opens)
    (m : (ParameterModels.supported T.ι).obj
        (specUnder.obj ((laurentUnderFunctor _).obj a)) ⟶
      boundedFlatCoefficientSupportedSectionModel
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι)
    (h : m.functor ⋙ (boundedFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι =
      ((ParameterModels.forget T.ι).app
        (specUnder.obj ((laurentUnderFunctor _).obj a))).functor ⋙
          ((parameterCoefficientRestriction Q).app ((laurentUnderFunctor _).obj a)).functor) :
    ((ParameterModels.supported T.ι).map (laurentSpecIso a.right).hom.op ≫ m).functor ⋙
      (boundedFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι =
    ((ParameterModels.forget T.ι).app
      (GlobalIndex.laurent.op.obj (specUnder.obj a))).functor ⋙
        (nativeLaurentMap Q a).functor := by
  have hn := congrArg Model.Hom.functor
    ((ParameterModels.forget T.ι).naturality (laurentSpecIso a.right).hom.op)
  change ((ParameterModels.supported T.ι).map (laurentSpecIso a.right).hom.op).functor ⋙
      ((ParameterModels.forget T.ι).app
        (specUnder.obj ((laurentUnderFunctor _).obj a))).functor =
    ((ParameterModels.forget T.ι).app
      (GlobalIndex.laurent.op.obj (specUnder.obj a))).functor ⋙
      ((ParameterModels.ambient Q.left).map (laurentSpecIso a.right).hom.op).functor at hn
  have ha := congrArg Model.Hom.functor (nativeLaurentMap_factor Q a)
  change ((ParameterModels.ambient Q.left).map (laurentSpecIso a.right).hom.op).functor ⋙
      ((parameterCoefficientRestriction Q).app ((laurentUnderFunctor _).obj a)).functor =
    (nativeLaurentMap Q a).functor at ha
  change ((ParameterModels.supported T.ι).map (laurentSpecIso a.right).hom.op).functor ⋙
    m.functor ⋙ (boundedFlatCoefficientSectionSupported
      (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι = _
  rw [h, ← Functor.assoc, hn, Functor.assoc, ha]

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The actual ambient Laurent corner uses the same affine index map and original row. -/
def ambientLaurentMap (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  (ParameterModels.supported (T).ι).map (laurentSpecIso a.right).hom.op ≫
    ambientComponent Q T ((laurentUnderFunctor _).obj a)

/-- The original forward ambient Laurent unit is retained under the complete comparison. -/
theorem ambientLaurentMap_unit (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (ambientLaurentMap Q T a).functor
      (supportedUnit (T).ι (specUnder.obj a))
      (boundedFlatCoefficientSupportedAmbientLaurentUnitIso Q T a) := by
  apply supportedLaurentMap_unit Q (T) a
  exact laurentComponent_forget Q (T) a _ _
    (ambientComponent_forget Q T ((laurentUnderFunctor _).obj a))

/-- The actual fiber Laurent corner uses the same affine index map and original row. -/
def fiberLaurentMap (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  (ParameterModels.supported (T ⊔ f.left.opensRange).ι).map (laurentSpecIso a.right).hom.op ≫
    fiberComponent f T ((laurentUnderFunctor _).obj a)

/-- The original forward fiber Laurent unit is retained under the complete comparison. -/
theorem fiberLaurentMap_unit
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (fiberLaurentMap f T a).functor
      (supportedUnit (T ⊔ f.left.opensRange).ι (specUnder.obj a))
      (boundedFlatCoefficientSupportedFiberLaurentUnitIso f T a) := by
  apply supportedLaurentMap_unit Q (T ⊔ f.left.opensRange) a
  exact laurentComponent_forget Q (T ⊔ f.left.opensRange) a _ _
    (fiberComponent_forget f T ((laurentUnderFunctor _).obj a))

/-- The actual open Laurent corner uses the same affine index map and original row. -/
def openLaurentMap (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  (ParameterModels.supported (f.left ⁻¹ᵁ T).ι).map (laurentSpecIso a.right).hom.op ≫
    openComponent f T ((laurentUnderFunctor _).obj a)

omit [IsOpenImmersion f.left] in
/-- The original forward open Laurent unit is retained under the complete comparison. -/
theorem openLaurentMap_unit
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (openLaurentMap f T a).functor
      (supportedUnit (f.left ⁻¹ᵁ T).ι (specUnder.obj a))
      (boundedFlatCoefficientSupportedFullOpenLaurentUnitIso f T a) := by
  apply supportedLaurentMap_unit P (f.left ⁻¹ᵁ T) a
  exact laurentComponent_forget P (f.left ⁻¹ᵁ T) a _ _
    (openComponent_forget f T ((laurentUnderFunctor _).obj a))

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
