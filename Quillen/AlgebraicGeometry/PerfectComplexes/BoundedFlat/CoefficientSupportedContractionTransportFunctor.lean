/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedPolynomialLaurentTransport
public import Quillen.KTheory.Bass.DiagramTransportGroupNaturality
public import Quillen.KTheory.Bass.TwoChartAdditive
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Original coefficient contraction transport on natural short rows

The already constructed polynomial and Laurent identifications on each compact native
coefficient pair row give a natural isomorphism between restriction followed by coefficient
contraction and original pair contraction followed by restriction. Its components are the
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
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The original native row transport is natural in every group-valued functor and map. -/
def boundedFlatCoefficientSupportedContractionWhiskeringIso :
    (Functor.whiskeringLeft (Under R) Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ
        AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactOpenPairRow f) ⋙
      contractionFunctor (underToLaurent R) (underToLaurentInvert R) ≅
    contractionFunctor
        (NatTrans.op Scheme.Bass.pairPlus)
        (NatTrans.op Scheme.Bass.pairMinus) ⋙
      (Functor.whiskeringLeft (Under R) Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ
        AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactOpenPairRow f) :=
  NatIso.ofComponents (boundedFlatCoefficientSupportedContractionTransportIso f) (by
    intro F G α
    apply NatTrans.ext
    funext a
    exact contractionTransportIso_groupMap
      (NatTrans.op Scheme.Bass.pairPlus)
      (NatTrans.op Scheme.Bass.pairMinus)
      (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientQuasiCompactOpenPairRow f)
      (boundedFlatCoefficientSupportedPolynomialIso f) (boundedFlatCoefficientSupportedLaurentIso f)
      (boundedFlatCoefficientSupportedPolynomialLaurentIso_plus f)
      (boundedFlatCoefficientSupportedPolynomialLaurentIso_minus f) α a)

/-- The same genuine transport compares all three objects and both maps of an original row. -/
def boundedFlatCoefficientSupportedContractionShortComplexIso
    (S : ShortComplex (Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})) :
    (S.map ((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ
        AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactOpenPairRow f))).map
      (contractionFunctor (underToLaurent R) (underToLaurentInvert R)) ≅
    (S.map (contractionFunctor
      (NatTrans.op Scheme.Bass.pairPlus)
      (NatTrans.op Scheme.Bass.pairMinus))).map
        ((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ
          AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactOpenPairRow f)) :=
  S.mapNatIso (boundedFlatCoefficientSupportedContractionWhiskeringIso f)

end Quillen.PerfectComplexes
