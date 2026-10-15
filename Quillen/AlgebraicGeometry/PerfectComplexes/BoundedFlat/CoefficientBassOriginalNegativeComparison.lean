/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassKZeroComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialLaurentTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassBottomComparison

/-!
# Original scheme negative K-groups at native finite-stage bottoms

The original scheme Bass recursion is compared with the actual native finite
Model stages. Genuine natural polynomial/Laurent product isomorphisms and the
original K-zero evaluation determine the comparison in every negative degree.
The ambient scheme is compact, and the assembled induction is natural in the
coefficient ring arrows. Supported groups and scheme-restriction naturality of the
assembled induction are outside this interface. No seed invertibility, transition
stability, telescope identification or classical TT identification is asserted.
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
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]

/-- The original scheme groups are naturally the bottom groups of every native finite stage. -/
def boundedFlatCoefficientAmbientNegativeKComparison :
    (i : ℕ) → boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i ≅
      boundedFlatCoefficientAmbientBassDiagram P i ⋙ stableHomotopyFunctor (-(i : ℤ))
  | 0 => boundedFlatCoefficientAmbientBassBottomZeroNatIso P
  | i + 1 => (boundedFlatCoefficientContractionTransportIso P (Bass.negativeKFunctor i)).symm ≪≫
      (Quillen.Bass.TwoChart.contractionFunctor (underToLaurent R) (underToLaurentInvert R)).mapIso
        (boundedFlatCoefficientAmbientNegativeKComparison i) ≪≫
      boundedFlatCoefficientAmbientBassBottomContractionIso P i

/-- Every original Laurent representative is preserved through the genuine product transport. -/
@[reassoc]
theorem boundedFlatCoefficientAmbientNegativeKComparison_π (i : ℕ) (a : Under R) :
    (Bass.negativeKFunctor i).map ((boundedFlatCoefficientLaurentIso P).hom.app a) ≫
      Bass.negativeKπ ((boundedFlatCoefficientQuasiCompactRow P).obj a).unop i ≫
        (boundedFlatCoefficientAmbientNegativeKComparison P (i + 1)).hom.app a =
    (boundedFlatCoefficientAmbientNegativeKComparison P i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (Quillen.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientAmbientBassDiagram P i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
        (boundedFlatCoefficientAmbientBassBottomContractionIso P i).hom.app a := by
  let τ := boundedFlatCoefficientContractionTransportIso P (Bass.negativeKFunctor i)
  let γ := boundedFlatCoefficientAmbientNegativeKComparison P i
  let β := boundedFlatCoefficientAmbientBassBottomContractionIso P i
  have ht : (Quillen.Bass.TwoChart.contractionπ (underToLaurent R)
      (underToLaurentInvert R)
      (boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i)).app a ≫
      τ.hom.app a =
    (Bass.negativeKFunctor i).map ((boundedFlatCoefficientLaurentIso P).hom.app a) ≫
      Bass.negativeKπ ((boundedFlatCoefficientQuasiCompactRow P).obj a).unop i :=
    boundedFlatCoefficientContractionTransportIso_π P (Bass.negativeKFunctor i) a
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

end Quillen.PerfectComplexes
