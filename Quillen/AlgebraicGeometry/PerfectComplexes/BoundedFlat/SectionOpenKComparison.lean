/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OpenComparison
public import Quillen.Waldhausen.GrothendieckComparison.SmallModel

/-!
# Original relative-open section evaluation on K-groups

The already exact evaluation and inverse into the actual common-universe relative-open model
induce an all-degree K-equivalence. Original universe lowering and bounded-flat inclusion then
compare to the original perfect relative-open category on the ambient affine scheme. The
forward comparisons retain original object-loop classes; no full-open restriction is inverted.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Original evaluation gives the all-degree equivalence with the bounded-flat relative model. -/
def boundedFlatAffineSectionOpenKEquiv (n : ℕ) :
    (boundedFlatAffineSectionOpenWaldhausen j).K n ≃*
      (boundedFlatPerfectOpenWaldhausen j).K n :=
  (KEquivOfExactEquivalence (boundedFlatAffineSectionOpenWaldhausen j)
    (boundedFlatPerfectOpenWaldhausen j).smallModel
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionOpenSmallEquivalence_exact j)
    (boundedFlatAffineSectionOpenSmallEquivalence_inverse_exact j) n).trans
      ((boundedFlatPerfectOpenWaldhausen j).smallModelKEquiv n).symm

/-- The same original exact evaluation K-map is retained before universe lowering. -/
theorem boundedFlatAffineSectionOpenKEquiv_apply (n : ℕ)
    (x : (boundedFlatAffineSectionOpenWaldhausen j).K n) :
    boundedFlatAffineSectionOpenKEquiv j n x =
      ((boundedFlatPerfectOpenWaldhausen j).smallModelKEquiv n).symm
        (KMap (boundedFlatAffineSectionOpenSmallEquivalence_exact j) n x) := rfl

/-- Relative-open evaluation preserves the unchanged original object-loop class. -/
@[simp] theorem boundedFlatAffineSectionOpenKEquiv_objectClass
    (S : BoundedFlatAffineSections R) :
    boundedFlatAffineSectionOpenKEquiv j 0
        ((boundedFlatAffineSectionOpenWaldhausen j).kZeroObjectClass S) =
      (boundedFlatPerfectOpenWaldhausen j).kZeroObjectClass
        ((boundedFlatAffineOriginalEvaluation R).obj S) := by
  rw [boundedFlatAffineSectionOpenKEquiv_apply]
  apply ((boundedFlatPerfectOpenWaldhausen j).smallModelKEquiv 0).injective
  rw [MulEquiv.apply_symm_apply, Structure.smallModelKEquiv_objectClass]
  exact KMap_kZeroObjectClass (boundedFlatAffineSectionOpenSmallEquivalence_exact j) S

/-- Original relative-open sections compute the unchanged ambient perfect relative-open groups. -/
def boundedFlatAffineSectionOpenPerfectKEquiv (n : ℕ) :
    (boundedFlatAffineSectionOpenWaldhausen j).K n ≃*
      (perfectOpenWeakWaldhausen j).K n :=
  (boundedFlatAffineSectionOpenKEquiv j n).trans (boundedFlatPerfectOpenKEquiv j n)

/-- The original coarse bounded-flat inclusion is applied after the actual evaluation comparison. -/
theorem boundedFlatAffineSectionOpenPerfectKEquiv_apply (n : ℕ)
    (x : (boundedFlatAffineSectionOpenWaldhausen j).K n) :
    boundedFlatAffineSectionOpenPerfectKEquiv j n x =
      boundedFlatPerfectOpenToPerfectOpenKMap j n (boundedFlatAffineSectionOpenKEquiv j n x) := rfl

/-- The perfect relative-open comparison retains the actual evaluated perfect object class. -/
@[simp] theorem boundedFlatAffineSectionOpenPerfectKEquiv_objectClass
    (S : BoundedFlatAffineSections R) :
    boundedFlatAffineSectionOpenPerfectKEquiv j 0
        ((boundedFlatAffineSectionOpenWaldhausen j).kZeroObjectClass S) =
      (perfectOpenWeakWaldhausen j).kZeroObjectClass
        ((boundedFlatPerfectInclusion (Spec R)).obj
          ((boundedFlatAffineOriginalEvaluation R).obj S)) := by
  rw [boundedFlatAffineSectionOpenPerfectKEquiv_apply,
    boundedFlatAffineSectionOpenKEquiv_objectClass]
  exact KMap_kZeroObjectClass (boundedFlatPerfectOpenInclusion_exact j) _

end Quillen.PerfectComplexes
