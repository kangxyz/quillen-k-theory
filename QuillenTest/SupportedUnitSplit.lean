/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedSplitExact
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedKStableComparison
import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedKGroups

/-! The actual supported canonical boundary retains the original quotient and coefficient maps. -/
noncomputable section
set_option linter.hashCommand false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
namespace Quillen.PerfectComplexes
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

example (n : ℕ) :
    boundedFlatCoefficientSupportedCanonicalBoundary f n ≫
      boundedFlatCoefficientSupportedInverseUnitQuotient f (n : ℤ) =
        contractionπ (underToLaurent R) (underToLaurentInvert R)
          (boundedFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1)) := by
  change (contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1)) ≫
    inv (boundedFlatCoefficientSupportedInverseUnitQuotient f (n : ℤ))) ≫
      boundedFlatCoefficientSupportedInverseUnitQuotient f (n : ℤ) = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

example (n : ℕ) :
    let F := laurentUnderFunctor R ⋙
      boundedFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1)
    let G := boundedFlatCoefficientSupportedStableGroupFunctor f (n : ℤ)
    let δ : F ⟶ G := boundedFlatCoefficientSupportedCanonicalBoundary f n
    ∀ {a b : Under R} (g : a ⟶ b), F.map g ≫ δ.app b = δ.app a ≫ G.map g := by
  intro F G δ a b g
  exact δ.naturality g

#print axioms boundedFlatCoefficientSupportedKStableEquiv_naturality
#print axioms boundedFlatCoefficientSupportedForwardUnitQuotient_isIso
#print axioms boundedFlatCoefficientSupportedInverseUnitQuotient_isIso
#print axioms boundedFlatCoefficientSupportedStageZeroChart_exact
#print axioms boundedFlatCoefficientSupportedCornerSplitting
#print axioms boundedFlatCoefficientSupportedInverseUnitSection_boundary
#print axioms boundedFlatCoefficientSupportedBoundarySplitting
#print axioms boundedFlatCoefficientSupportedMiddleSequence_map_exact
end Quillen.PerfectComplexes

#print axioms Quillen.Waldhausen.IteratedS.prespectrumIsoHomotopy_stableOperation_symm
#print axioms Quillen.KTheory.Bass.LaurentSeed.Track.bassLeft_isIso_of_seed
#print axioms Quillen.KTheory.Bass.LaurentSeed.ModelAction.symm_stableUnitQuotient
