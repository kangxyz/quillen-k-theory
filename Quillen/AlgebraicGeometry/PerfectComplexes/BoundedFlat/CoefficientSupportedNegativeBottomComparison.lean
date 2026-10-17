/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedKZeroComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedPolynomialLaurentTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassBottomComparison

/-!
# Original supported negative K-groups at actual finite native bottoms

The original supported Bass recursion on scheme/open pairs is naturally the
bottom stable group of each finite supported Model stage. The comparison uses
the original supported K-zero evaluation and the genuine pair polynomial/Laurent
isomorphisms. Its representative equation retains the original supported quotient
and the actual finite-stage cone inclusion and signed shift. Compactness of the
ambient scheme suffices for this finite comparison. No invertibility of supported
transitions or comparison with their telescope is asserted.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The original supported groups are naturally the bottom groups of every native finite stage. -/
def boundedFlatCoefficientSupportedNegativeKComparison :
    (i : ℕ) → boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i ≅
      boundedFlatCoefficientSupportedBassDiagram f i ⋙ stableHomotopyFunctor (-(i : ℤ))
  | 0 => boundedFlatCoefficientSupportedBassBottomZeroNatIso f
  | i + 1 => (boundedFlatCoefficientSupportedContractionTransportIso f
      (Bass.supportedNegativeKFunctor i)).symm ≪≫
      (Quillen.Bass.TwoChart.contractionFunctor (underToLaurent R) (underToLaurentInvert R)).mapIso
        (boundedFlatCoefficientSupportedNegativeKComparison i) ≪≫
      boundedFlatCoefficientSupportedBassBottomContractionIso f i

/-- Every original supported Laurent representative is preserved by genuine product transport. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedNegativeKComparison_π (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKFunctor i).map
      ((boundedFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop i ≫
        (boundedFlatCoefficientSupportedNegativeKComparison f (i + 1)).hom.app a =
    (boundedFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (Quillen.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientSupportedBassDiagram f i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
        (boundedFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a := by
  let τ := boundedFlatCoefficientSupportedContractionTransportIso f
    (Bass.supportedNegativeKFunctor i)
  let γ := boundedFlatCoefficientSupportedNegativeKComparison f i
  let β := boundedFlatCoefficientSupportedBassBottomContractionIso f i
  have ht : (Quillen.Bass.TwoChart.contractionπ (underToLaurent R)
      (underToLaurentInvert R)
      (boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i)).app a ≫
      τ.hom.app a =
    (Bass.supportedNegativeKFunctor i).map
      ((boundedFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop i :=
    boundedFlatCoefficientSupportedContractionTransportIso_π f (Bass.supportedNegativeKFunctor i) a
  change _ ≫ _ ≫ (τ.inv.app a ≫
    (Quillen.Bass.TwoChart.contractionMap (underToLaurent R)
      (underToLaurentInvert R) γ.hom).app a ≫ β.hom.app a) = _
  have hcancel : τ.hom.app a ≫ τ.inv.app a ≫
      (Quillen.Bass.TwoChart.contractionMap (underToLaurent R)
        (underToLaurentInvert R) γ.hom).app a ≫ β.hom.app a =
    (Quillen.Bass.TwoChart.contractionMap (underToLaurent R)
      (underToLaurentInvert R) γ.hom).app a ≫ β.hom.app a :=
    (τ.app a).hom_inv_id_assoc _
  rw [← Category.assoc, ← ht, Category.assoc, hcancel]
  exact Quillen.Bass.TwoChart.contractionMap_π_assoc (underToLaurent R)
    (underToLaurentInvert R) γ.hom a (β.hom.app a)

/-- The same original quotient formula includes the actual cone inclusion and signed shift. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedNegativeKComparison_π_cone (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKFunctor i).map
      ((boundedFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop i ≫
        (boundedFlatCoefficientSupportedNegativeKComparison f (i + 1)).hom.app a =
    (boundedFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (mappingConeInclusion (StrictSquare.comparison
          ((boundedFlatCoefficientSupportedBassDiagram f i).mapArrow.mapArrow.obj
            (laurentUnderSquare R a)))) ≫
        (Quillen.KTheory.Bass.modelDiagramBottomSuccessorIso
          (boundedFlatCoefficientSupportedModelFunctor f) i).inv.app a := by
  rw [boundedFlatCoefficientSupportedNegativeKComparison_π,
    boundedFlatCoefficientSupportedBassBottomContractionIso_π]

end Quillen.PerfectComplexes
