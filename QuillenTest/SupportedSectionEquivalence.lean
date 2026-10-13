/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionWaldhausen

/-!
# Original supported evaluation and Waldhausen consumers

The same original evaluated complexes and chain maps, supported cofibrations, actual pushout
squares and unchanged pointwise zero are retained by the proved genuine evaluation equivalence.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.SupportedSectionEquivalence

open Quillen
open PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineSupportedSectionEquivalence boundedFlatAffineSupportedEvaluation

/-- Every original supported complex is covered by the unchanged evaluation with its actual counit.
-/
def originalSupportedComplexCounit (K : (boundedFlatPerfectSupported j).FullSubcategory) :
    (boundedFlatAffineSupportedEvaluation j).obj
      ((boundedFlatAffineSupportedSectionEquivalence j).inverse.obj K) ≅ K :=
  boundedFlatAffineSupportedEvaluationCounit j K

/-- Every arrow between original evaluated supported objects lifts under the same evaluation. -/
theorem original_supported_arrow_lift (X Y : BoundedFlatAffineSupportedSections j)
    (a : (boundedFlatAffineSupportedEvaluation j).obj X ⟶
      (boundedFlatAffineSupportedEvaluation j).obj Y) :
    ∃ b : X ⟶ Y, (boundedFlatAffineSupportedEvaluation j).map b = a :=
  (boundedFlatAffineSupportedEvaluation j).map_surjective a

/-- Original evaluation is faithful on the actual supported section arrows. -/
theorem original_supported_arrow_reflection {X Y : BoundedFlatAffineSupportedSections j}
    (a b : X ⟶ Y) (h : (boundedFlatAffineSupportedEvaluation j).map a =
      (boundedFlatAffineSupportedEvaluation j).map b) : a = b :=
  (boundedFlatAffineSupportedEvaluation j).map_injective h

/-- The Waldhausen point is the unchanged original source-independent section zero. -/
theorem original_waldhausen_zero :
    (boundedFlatAffineSupportedSectionWaldhausen j).zero.obj =
      boundedFlatAffineSectionZero R := rfl

/-- Weak equivalences retain the exact original evaluated chain map and its quasi-isomorphism. -/
theorem original_supported_weak_map {X Y : BoundedFlatAffineSupportedSections j} (a : X ⟶ Y) :
    (boundedFlatAffineSupportedSectionWaldhausen j).weq a ↔
      QuasiIso ((boundedFlatAffineSupportedEvaluation j).map a).hom :=
  boundedFlatAffineSupportedSectionWaldhausen_weq_iff j a

/-- An actual supported cofibration pushout retains every original evaluated edge. -/
theorem original_supported_pushout {A B D P : BoundedFlatAffineSupportedSections j}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {k : D ⟶ P}
    (hi : (boundedFlatAffineSupportedSectionWaldhausen j).cof i) (hp : IsPushout i f g k) :
    IsPushout ((boundedFlatAffineSupportedEvaluation j).map i)
      ((boundedFlatAffineSupportedEvaluation j).map f)
      ((boundedFlatAffineSupportedEvaluation j).map g)
      ((boundedFlatAffineSupportedEvaluation j).map k) :=
  (boundedFlatAffineSupportedEvaluation_exact j).pushout hi hp

end QuillenTest.SupportedSectionEquivalence
