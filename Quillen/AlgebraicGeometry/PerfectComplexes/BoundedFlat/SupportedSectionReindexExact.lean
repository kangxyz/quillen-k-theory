/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionWaldhausen
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionCoefficientIso
public import Quillen.Waldhausen.ExtensionCategory.ExactTransport

/-!
# Original supported coefficient reindexing is Waldhausen-exact

The genuine geometric supported pullback and original evaluation comparison prove exactness
of the unchanged supported section reindexing. The existing actual evaluation equivalence
reflects zero objects and pushouts. Coefficient comparison remains a natural isomorphism;
no strict naturality of geometric evaluation or negative localization is inferred.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineSupportedSectionEquivalence boundedFlatAffineSupportedEvaluation

/-- The original reindexed evaluation is exact through its genuine geometric coefficient iso. -/
theorem boundedFlatAffineSupportedSectionsMap_evaluation_exact :
    Waldhausen.IsExact (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatPerfectSupportedWaldhausen j').cof (boundedFlatPerfectSupportedWaldhausen j').weq
      (boundedFlatAffineSupportedSectionsMap j j' f l h ⋙
        boundedFlatAffineSupportedEvaluation j') :=
  Waldhausen.ExtensionCategory.isExact_of_natIso
    (boundedFlatAffineSupportedSectionWaldhausen j) (boundedFlatPerfectSupportedWaldhausen j')
    ((boundedFlatAffineSupportedEvaluation_exact j).comp
      (boundedFlatPerfectSupportedPullback_exact
        (boundedFlatAffineSupportedPairSquare j j' f l h)))
    (boundedFlatAffineSupportedSectionCoefficientIso j j' f l h).symm

/-- Every unchanged supported coefficient map is exact, with its actual original open square. -/
theorem boundedFlatAffineSupportedSectionsMap_exact :
    Waldhausen.IsExact (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatAffineSupportedSectionWaldhausen j').cof
      (boundedFlatAffineSupportedSectionWaldhausen j').weq
      (boundedFlatAffineSupportedSectionsMap j j' f l h) where
  zero hx := IsZero.of_full_of_faithful_of_isZero (boundedFlatAffineSupportedEvaluation j') _
    ((boundedFlatAffineSupportedSectionsMap_evaluation_exact j j' f l h).zero hx)
  cofibration a ha := (boundedFlatAffineSupportedSectionWaldhausen_cof_iff j' _).mpr
    ((boundedFlatAffineSupportedSectionsMap_evaluation_exact j j' f l h).cofibration a ha)
  weak a ha := (boundedFlatAffineSupportedSectionWaldhausen_weq_iff j' _).mpr
    ((boundedFlatAffineSupportedSectionsMap_evaluation_exact j j' f l h).weak a ha)
  pushout hi hp := by
    apply IsPushout.of_map_of_faithful (boundedFlatAffineSupportedEvaluation j')
    exact (boundedFlatAffineSupportedSectionsMap_evaluation_exact j j' f l h).pushout hi hp

end Quillen.PerfectComplexes
