/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionReindexExact

/-!
# Original supported coefficient exactness consumers

The actual coefficient and open-side arrows, supported cofibration/weak maps, four pushout
edges, and literal source-independent zero remain explicit. The geometric coefficient
comparison is a proved natural isomorphism, with its original forgetful squares retained.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.SupportedSectionReindexExact

open Quillen
open PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineSupportedSectionEquivalence boundedFlatAffineSupportedEvaluation

/-- The geometric square uses the original coefficient and open-side maps literally. -/
theorem original_pair_square :
    (boundedFlatAffineSupportedPairSquare j j' f l h).hom.left = l ∧
      (boundedFlatAffineSupportedPairSquare j j' f l h).hom.right = Spec.map f := ⟨rfl, rfl⟩

/-- The original coefficient functor preserves actual supported cofibrations. -/
theorem original_coefficient_cofibration {X Y : BoundedFlatAffineSupportedSections j}
    (a : X ⟶ Y) (ha : (boundedFlatAffineSupportedSectionWaldhausen j).cof a) :
    (boundedFlatAffineSupportedSectionWaldhausen j').cof
      ((boundedFlatAffineSupportedSectionsMap j j' f l h).map a) :=
  (boundedFlatAffineSupportedSectionsMap_exact j j' f l h).cofibration a ha

/-- The unchanged reindexed evaluated chain map remains a quasi-isomorphism. -/
theorem original_coefficient_quasiIso {X Y : BoundedFlatAffineSupportedSections j}
    (a : X ⟶ Y) (ha : (boundedFlatAffineSupportedSectionWaldhausen j).weq a) :
    QuasiIso ((boundedFlatAffineSupportedEvaluation j').map
      ((boundedFlatAffineSupportedSectionsMap j j' f l h).map a)).hom :=
  (boundedFlatAffineSupportedSectionWaldhausen_weq_iff j' _).mp
    ((boundedFlatAffineSupportedSectionsMap_exact j j' f l h).weak a ha)

/-- Every actual supported cofibration pushout keeps its four original reindexed arrows. -/
theorem original_coefficient_pushout {A B D P : BoundedFlatAffineSupportedSections j}
    {i : A ⟶ B} {a : A ⟶ D} {b : B ⟶ P} {k : D ⟶ P}
    (hi : (boundedFlatAffineSupportedSectionWaldhausen j).cof i) (hp : IsPushout i a b k) :
    IsPushout ((boundedFlatAffineSupportedSectionsMap j j' f l h).map i)
      ((boundedFlatAffineSupportedSectionsMap j j' f l h).map a)
      ((boundedFlatAffineSupportedSectionsMap j j' f l h).map b)
      ((boundedFlatAffineSupportedSectionsMap j j' f l h).map k) :=
  (boundedFlatAffineSupportedSectionsMap_exact j j' f l h).pushout hi hp

/-- The exact original coefficient functor retains the actual supported chosen zero literally. -/
theorem original_coefficient_zero :
    (boundedFlatAffineSupportedSectionsMap j j' f l h).obj
        (boundedFlatAffineSupportedSectionWaldhausen j).zero =
      (boundedFlatAffineSupportedSectionWaldhausen j').zero :=
  boundedFlatAffineSupportedSectionsMap_sectionZero j j' f l h

/-- Original geometric evaluation and original pair pullback compare through an actual iso. -/
def originalCoefficientComparison (s : BoundedFlatAffineSupportedSections j) :
    (boundedFlatAffineSupportedEvaluation j').obj
        ((boundedFlatAffineSupportedSectionsMap j j' f l h).obj s) ≅
      (boundedFlatPerfectSupportedPullback (boundedFlatAffineSupportedPairSquare j j' f l h)).obj
        ((boundedFlatAffineSupportedEvaluation j).obj s) :=
  (boundedFlatAffineSupportedSectionCoefficientIso j j' f l h).app s

end QuillenTest.SupportedSectionReindexExact
