/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientContractionTransportFunctor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCornerComplex
public import Quillen.KTheory.Bass.SchemeMiddleComparison

/-!
# The original coefficient Bass middle row under native scheme transport

The actual polynomial/product isomorphism preserves the literal common projection. Together
with the already checked positive and negative chart squares, it identifies the entire
original coefficient middle row with the restricted native scheme row. The construction
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
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]

/-- Both literal coefficient chart inclusions agree at the original common corner. -/
theorem boundedFlatCoefficientCommonCorner :
    polynomialUnderCoefficient R ≫ underToLaurent R =
      polynomialUnderCoefficient R ≫ underToLaurentInvert R := by
  apply NatTrans.ext
  funext a
  exact (polynomialUnderCoefficient_toLaurent R a).trans
    (polynomialUnderCoefficient_toLaurentInvert R a).symm

/-- The actual polynomial/product comparison retains the original common projection. -/
@[reassoc]
theorem boundedFlatCoefficientPolynomialIso_corner (a : Under R) :
    (boundedFlatCoefficientQuasiCompactRow P).map ((polynomialUnderCoefficient R).app a) ≫
      (boundedFlatCoefficientPolynomialIso P).hom.app a =
    (NatTrans.op Scheme.PolynomialLaurent.Relative.polynomialProjection).app
      ((boundedFlatCoefficientQuasiCompactRow P).obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  change (polynomialIso P a).inv ≫ polynomialProjection P a = _
  rw [← polynomialIso_hom_fst P a, Iso.inv_hom_id_assoc]
  rfl

/-- Actual transport on all three groups and both original middle arrows. -/
def boundedFlatCoefficientMiddleTransportIso
    (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    middleComplex (polynomialUnderCoefficient R) (underToLaurent R)
      (underToLaurentInvert R) (boundedFlatCoefficientCommonCorner (R := R))
      (boundedFlatCoefficientQuasiCompactRow P ⋙ F) ≅
    (Scheme.PolynomialLaurent.Relative.bassMiddleComplex F).map
      ((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactSchemes.{u}ᵒᵖ
        AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactRow P)) := by
  let T := boundedFlatCoefficientQuasiCompactRow P
  let W := (Functor.whiskeringLeft (Under R) Scheme.QuasiCompactSchemes.{u}ᵒᵖ
    AddCommGrpCat.{w}).obj T
  let e := transportDifferenceIso
    (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
    (NatTrans.op Scheme.PolynomialLaurent.Relative.minus)
    (underToLaurent R) (underToLaurentInvert R) T
    (boundedFlatCoefficientPolynomialIso P) (boundedFlatCoefficientLaurentIso P)
    (boundedFlatCoefficientPolynomialLaurentIso_plus P)
    (boundedFlatCoefficientPolynomialLaurentIso_minus P) F
  refine (ShortComplex.isoMk
    (S₂ := (middleComplex
      (NatTrans.op Scheme.PolynomialLaurent.Relative.polynomialProjection)
      (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
      (NatTrans.op Scheme.PolynomialLaurent.Relative.minus)
      Scheme.PolynomialLaurent.Relative.bassCommonCorner F).map W)
    (Iso.refl (T ⋙ F))
    (Functor.isoWhiskerRight e Arrow.leftFunc)
    (Functor.isoWhiskerRight (boundedFlatCoefficientLaurentIso P) F) ?_ ?_) ≪≫
      W.mapShortComplex.mapIso (Scheme.PolynomialLaurent.Relative.bassMiddlePointwiseIso F)
  · apply NatTrans.ext
    funext a
    change 𝟙 _ ≫ biprod.lift _ _ =
      biprod.lift (F.map (T.map ((polynomialUnderCoefficient R).app a)))
        (F.map (T.map ((polynomialUnderCoefficient R).app a))) ≫
      biprod.map (F.map ((boundedFlatCoefficientPolynomialIso P).hom.app a))
        (F.map ((boundedFlatCoefficientPolynomialIso P).hom.app a))
    rw [Category.id_comp]
    apply biprod.hom_ext
    · rw [biprod.lift_fst, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
        ← F.map_comp]
      exact congrArg F.map (boundedFlatCoefficientPolynomialIso_corner P a).symm
    · rw [biprod.lift_snd, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
        ← F.map_comp]
      exact congrArg F.map (boundedFlatCoefficientPolynomialIso_corner P a).symm
  · apply NatTrans.ext
    funext a
    exact (e.hom.app a).w

/-- The pointwise general middle row specializes to the unchanged original coefficient K-row.
-/
def boundedFlatCoefficientKMiddleIso (n : ℕ) :
    boundedFlatCoefficientMiddleSequence P n ≅
      middleComplex (polynomialUnderCoefficient R) (underToLaurent R)
        (underToLaurentInvert R) (boundedFlatCoefficientCommonCorner (R := R))
        (boundedFlatCoefficientKAddFunctor P n) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

end Quillen.PerfectComplexes
