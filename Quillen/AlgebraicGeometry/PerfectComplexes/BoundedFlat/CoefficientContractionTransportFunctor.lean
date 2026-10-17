/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialLaurentTransport
public import Quillen.KTheory.Bass.DiagramTransportGroupNaturality
public import Quillen.KTheory.Bass.TwoChartAdditive
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Original coefficient contraction transport on natural short rows

The already constructed polynomial and Laurent identifications on each compact native
coefficient row give a natural isomorphism between restriction followed by coefficient
contraction and original scheme contraction followed by restriction. Its components are the
unchanged quotient transport. Consequently it compares actual short complexes, preserving
their original maps, without an exactness assumption or a replacement of the Bass boundary.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
universe u w
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]

/-- The original native row transport is natural in every group-valued functor and map. -/
def boundedFlatCoefficientContractionWhiskeringIso :
    (Functor.whiskeringLeft (Under R) Scheme.QuasiCompactSchemes.{u}ᵒᵖ
        AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactRow P) ⋙
      contractionFunctor (underToLaurent R) (underToLaurentInvert R) ≅
    contractionFunctor
        (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
        (NatTrans.op Scheme.PolynomialLaurent.Relative.minus) ⋙
      (Functor.whiskeringLeft (Under R) Scheme.QuasiCompactSchemes.{u}ᵒᵖ
        AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactRow P) :=
  NatIso.ofComponents (boundedFlatCoefficientContractionTransportIso P) (by
    intro F G α
    apply NatTrans.ext
    funext a
    exact contractionTransportIso_groupMap
      (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
      (NatTrans.op Scheme.PolynomialLaurent.Relative.minus)
      (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientQuasiCompactRow P)
      (boundedFlatCoefficientPolynomialIso P) (boundedFlatCoefficientLaurentIso P)
      (boundedFlatCoefficientPolynomialLaurentIso_plus P)
      (boundedFlatCoefficientPolynomialLaurentIso_minus P) α a)

/-- The same genuine transport compares all three objects and both maps of an original row. -/
def boundedFlatCoefficientContractionShortComplexIso
    (S : ShortComplex (Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})) :
    (S.map ((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactSchemes.{u}ᵒᵖ
        AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactRow P))).map
      (contractionFunctor (underToLaurent R) (underToLaurentInvert R)) ≅
    (S.map (contractionFunctor
      (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
      (NatTrans.op Scheme.PolynomialLaurent.Relative.minus))).map
        ((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactSchemes.{u}ᵒᵖ
          AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactRow P)) :=
  S.mapNatIso (boundedFlatCoefficientContractionWhiskeringIso P)

end Quillen.PerfectComplexes
