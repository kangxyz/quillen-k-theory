/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedPolynomialLaurentTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedForget
public import Quillen.KTheory.Bass.DiagramTransportGroupNaturality

/-!
# Original support forgetting under coefficient contraction transport

The original pair-to-ambient transport has the same geometric Laurent map as the ambient
coefficient transport. Its quotient equation and generic group-map naturality give the
actual forget-support square required by the original negative-group recursion.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Forgetting the pair retains exactly the original ambient Laurent transport. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedContractionTransportIso_base
    (G : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (a : Under R) :
    (boundedFlatCoefficientSupportedContractionTransportIso f
      (quasiCompactOpenPairsBase.op ⋙ G)).hom.app a ≫
        (Bass.supportedContractionForgetIso G).hom.app
          ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) =
      (boundedFlatCoefficientContractionTransportIso Q G).hom.app a := by
  apply (cancel_epi ((contractionπ (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientQuasiCompactRow Q ⋙ G)).app a)).mp
  erw [boundedFlatCoefficientSupportedContractionTransportIso_π_assoc f
    (quasiCompactOpenPairsBase.op ⋙ G) a,
    boundedFlatCoefficientContractionTransportIso_π Q G a]
  unfold Bass.supportedContractionForgetIso
  rw [contractionTransportIso_π]
  change G.map ((boundedFlatCoefficientLaurentIso Q).hom.app a) ≫
      G.map (𝟙 _) ≫ _ = _
  rw [G.map_id, Category.id_comp]
  rfl

/-- Every original group-valued support-forgetting map retains its actual coefficient transport. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedContractionTransportIso_forget
    {F : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    {G : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (α : F ⟶ quasiCompactOpenPairsBase.op ⋙ G) (a : Under R) :
    (contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerLeft (boundedFlatCoefficientQuasiCompactOpenPairRow f) α)).app a ≫
        (boundedFlatCoefficientContractionTransportIso Q G).hom.app a =
      (boundedFlatCoefficientSupportedContractionTransportIso f F).hom.app a ≫
        (contractionMap (NatTrans.op Scheme.Bass.pairPlus)
          (NatTrans.op Scheme.Bass.pairMinus) α).app
          ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
        (Bass.supportedContractionForgetIso G).hom.app
          ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) := by
  rw [← boundedFlatCoefficientSupportedContractionTransportIso_base f G a,
    ← Category.assoc]
  have h := contractionTransportIso_groupMap
    (NatTrans.op Scheme.Bass.pairPlus) (NatTrans.op Scheme.Bass.pairMinus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientQuasiCompactOpenPairRow f)
    (boundedFlatCoefficientSupportedPolynomialIso f) (boundedFlatCoefficientSupportedLaurentIso f)
    (boundedFlatCoefficientSupportedPolynomialLaurentIso_plus f)
    (boundedFlatCoefficientSupportedPolynomialLaurentIso_minus f) α a
  rw [show (contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerLeft (boundedFlatCoefficientQuasiCompactOpenPairRow f) α)).app a ≫
        (boundedFlatCoefficientSupportedContractionTransportIso f
          (quasiCompactOpenPairsBase.op ⋙ G)).hom.app a = _ from h]
  exact Category.assoc _ _ _

/-- The original recursive supported forget map commutes with the unchanged coefficient transport.
-/
theorem boundedFlatCoefficientSupportedContractionTransportIso_negativeForget (i : ℕ) :
    (boundedFlatCoefficientSupportedContractionTransportIso f
      (Bass.supportedNegativeKFunctor i)).hom ≫
        Functor.whiskerLeft (boundedFlatCoefficientQuasiCompactOpenPairRow f)
          (Bass.supportedNegativeKForgetNat (i + 1)) =
      (contractionFunctor (underToLaurent R) (underToLaurentInvert R)).map
        (Functor.whiskerLeft (boundedFlatCoefficientQuasiCompactOpenPairRow f)
          (Bass.supportedNegativeKForgetNat i)) ≫
        (boundedFlatCoefficientContractionTransportIso Q (Bass.negativeKFunctor i)).hom := by
  apply NatTrans.ext
  funext a
  exact (boundedFlatCoefficientSupportedContractionTransportIso_forget f
    (Bass.supportedNegativeKForgetNat i) a).symm

end Quillen.PerfectComplexes
