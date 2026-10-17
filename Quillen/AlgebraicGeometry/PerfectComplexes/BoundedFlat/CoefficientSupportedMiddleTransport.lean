/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedContractionTransportFunctor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedSplitExact
public import Quillen.KTheory.Bass.OpenPairContractionMiddle

/-!
# The original coefficient Bass middle row under native open-pair transport

The actual polynomial/product isomorphism preserves the literal common projection. Together
with the already checked positive and negative chart squares, it identifies the entire
original coefficient middle row with the restricted native open-pair row. The construction
retains the original corner, signed difference and quotient inputs.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u w
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The actual polynomial/product comparison retains the original common projection. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedPolynomialIso_corner (a : Under R) :
    (boundedFlatCoefficientQuasiCompactOpenPairRow f).map ((polynomialUnderCoefficient R).app a) ≫
      (boundedFlatCoefficientSupportedPolynomialIso f).hom.app a =
    (NatTrans.op Scheme.Bass.pairPolynomialProjection).app
      ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · change (polynomialIso P a).inv ≫ polynomialProjection P a = _
    rw [← polynomialIso_hom_fst P a, Iso.inv_hom_id_assoc]
    rfl
  · change (polynomialIso Q a).inv ≫ polynomialProjection Q a = _
    rw [← polynomialIso_hom_fst Q a, Iso.inv_hom_id_assoc]
    rfl

/-- Actual transport on all three groups and both original middle arrows. -/
def boundedFlatCoefficientSupportedMiddleTransportIso
    (F : Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    middleComplex (polynomialUnderCoefficient R) (underToLaurent R)
      (underToLaurentInvert R) (boundedFlatCoefficientSupportedCommonCorner (R := R))
      (boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ F) ≅
    (Scheme.Bass.pairBassMiddleComplex F).map
      ((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ
        AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactOpenPairRow f)) := by
  let T := boundedFlatCoefficientQuasiCompactOpenPairRow f
  let W := (Functor.whiskeringLeft (Under R) Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ
    AddCommGrpCat.{w}).obj T
  let e := transportDifferenceIso
    (NatTrans.op Scheme.Bass.pairPlus)
    (NatTrans.op Scheme.Bass.pairMinus)
    (underToLaurent R) (underToLaurentInvert R) T
    (boundedFlatCoefficientSupportedPolynomialIso f) (boundedFlatCoefficientSupportedLaurentIso f)
    (boundedFlatCoefficientSupportedPolynomialLaurentIso_plus f)
    (boundedFlatCoefficientSupportedPolynomialLaurentIso_minus f) F
  refine (ShortComplex.isoMk
    (S₂ := (middleComplex
      (NatTrans.op Scheme.Bass.pairPolynomialProjection)
      (NatTrans.op Scheme.Bass.pairPlus)
      (NatTrans.op Scheme.Bass.pairMinus)
      Scheme.Bass.pairCommonCorner F).map W)
    (Iso.refl (T ⋙ F))
    (Functor.isoWhiskerRight e Arrow.leftFunc)
    (Functor.isoWhiskerRight (boundedFlatCoefficientSupportedLaurentIso f) F) ?_ ?_) ≪≫
      W.mapShortComplex.mapIso (Scheme.Bass.pairBassMiddlePointwiseIso F)
  · apply NatTrans.ext
    funext a
    change 𝟙 _ ≫ biprod.lift _ _ =
      biprod.lift (F.map (T.map ((polynomialUnderCoefficient R).app a)))
        (F.map (T.map ((polynomialUnderCoefficient R).app a))) ≫
      biprod.map (F.map ((boundedFlatCoefficientSupportedPolynomialIso f).hom.app a))
        (F.map ((boundedFlatCoefficientSupportedPolynomialIso f).hom.app a))
    rw [Category.id_comp]
    apply biprod.hom_ext
    · rw [biprod.lift_fst, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
        ← F.map_comp]
      exact congrArg F.map (boundedFlatCoefficientSupportedPolynomialIso_corner f a).symm
    · rw [biprod.lift_snd, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
        ← F.map_comp]
      exact congrArg F.map (boundedFlatCoefficientSupportedPolynomialIso_corner f a).symm
  · apply NatTrans.ext
    funext a
    exact (e.hom.app a).w

end Quillen.PerfectComplexes
