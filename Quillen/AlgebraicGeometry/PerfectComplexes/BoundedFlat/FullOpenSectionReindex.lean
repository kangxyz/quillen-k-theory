/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionWaldhausen
public import Quillen.CategoryTheory.FiberedCategory.CocartesianSectionTransition
public import Quillen.Waldhausen.ExtensionCategory.ExactTransport

/-!
# Exact original full-open coefficient reindexing

The original section transition compares reindexed identity evaluation with actual pullback
along the original map of fixed open fibers. Its genuine natural isomorphism transports
exactness. Faithful full evaluation reflects zero objects and pushouts. No equality of
geometric pullback functors is substituted for the original comparison isomorphism.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineFullOpenOriginalEvaluation

/-- The original transition, with its actual coefficient-evaluation comparison. -/
def boundedFlatAffineFullOpenSectionCoefficientIso {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenSectionsMap j f ⋙
        boundedFlatAffineFullOpenOriginalEvaluation j b ≅
      boundedFlatAffineFullOpenOriginalEvaluation j a ⋙
        boundedFlatPerfectPullback (openMap j f) := by
  unfold boundedFlatAffineFullOpenOriginalEvaluation
  exact eqToIso (Quillen.CategoryTheory.GrothendieckSections.originalEvaluation_reindex
    (boundedFlatAffineFullOpenPseudofunctor j) a f) ≪≫
  (Quillen.CategoryTheory.GrothendieckSections.originalEvaluationTransitionIso
    (boundedFlatAffineFullOpenPseudofunctor j) a (Under.mk f)).symm

/-- Evaluation after the unchanged original reindexing is exact. -/
theorem boundedFlatAffineFullOpenSectionsMap_evaluation_exact {a b : Under R} (f : a ⟶ b) :
    Waldhausen.IsExact (boundedFlatAffineFullOpenSectionWaldhausen j a).cof
      (boundedFlatAffineFullOpenSectionWaldhausen j a).weq
      (boundedFlatPerfectWaldhausen (openSpace j b)).cof
      (boundedFlatPerfectWaldhausen (openSpace j b)).weq
      (boundedFlatAffineFullOpenSectionsMap j f ⋙
        boundedFlatAffineFullOpenOriginalEvaluation j b) :=
  Waldhausen.ExtensionCategory.isExact_of_natIso
    (boundedFlatAffineFullOpenSectionWaldhausen j a)
    (boundedFlatPerfectWaldhausen (openSpace j b))
    ((boundedFlatAffineFullOpenOriginalEvaluation_exact j a).comp
      (boundedFlatPerfectPullback_exact (openMap j f)))
    (boundedFlatAffineFullOpenSectionCoefficientIso j f).symm

/-- The actual coefficient functor preserves zero, cofibrations, weak maps and pushouts. -/
theorem boundedFlatAffineFullOpenSectionsMap_exact {a b : Under R} (f : a ⟶ b) :
    Waldhausen.IsExact (boundedFlatAffineFullOpenSectionWaldhausen j a).cof
      (boundedFlatAffineFullOpenSectionWaldhausen j a).weq
      (boundedFlatAffineFullOpenSectionWaldhausen j b).cof
      (boundedFlatAffineFullOpenSectionWaldhausen j b).weq
      (boundedFlatAffineFullOpenSectionsMap j f) where
  zero hx := IsZero.of_full_of_faithful_of_isZero
    (boundedFlatAffineFullOpenOriginalEvaluation j b) _
    ((boundedFlatAffineFullOpenSectionsMap_evaluation_exact j f).zero hx)
  cofibration g hg :=
    (boundedFlatAffineFullOpenSectionsMap_evaluation_exact j f).cofibration g hg
  weak g hg := (boundedFlatAffineFullOpenSectionsMap_evaluation_exact j f).weak g hg
  pushout hi hp := by
    apply IsPushout.of_map_of_faithful (boundedFlatAffineFullOpenOriginalEvaluation j b)
    exact (boundedFlatAffineFullOpenSectionsMap_evaluation_exact j f).pushout hi hp

end Quillen.PerfectComplexes
