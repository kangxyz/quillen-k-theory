/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenGrading
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalCofinality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionKComparison

/-!
# Cofinality of the original global native section restriction

One evaluation K-equivalence bridge accounts for the native section and fiber
hom universes. Its original exact functor and natural-isomorphism square retain
the installed bounded-flat restriction map. The original perfect comparisons
then transport global cofinality to the unchanged section restriction.

Quasi-compactness is required only for the perfect comparisons, and
quasi-separatedness only for installed global cofinality. There is no supplied
density, roof, K-zero image, coefficient-flatness or affine-scheme premise.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen AlgebraicGeometry.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation

/-- The same evaluation computes the original coarse relative-open bounded-flat groups. -/
def boundedFlatCoefficientOpenKEquiv (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientOpenWaldhausen f a).K n ≃*
      (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).K n :=
  boundedFlatCoefficientEvaluationKEquiv (boundedFlatCoefficientOpenWaldhausen f a)
    (boundedFlatPerfectOpenWaldhausen (schemeMap f a))
    (boundedFlatCoefficientSectionEquivalence (op Q, a))
    (boundedFlatCoefficientOpenEvaluation_coarse_exact f a)
    (boundedFlatCoefficientOpenEquivalence_inverse_exact f a) n

/-- The actual geometric evaluation square retains the original bounded-flat restriction. -/
theorem boundedFlatCoefficientOpenRestriction_KComparison (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientOpenWaldhausen f a).K n) :
    boundedFlatCoefficientSectionKEquiv (op P, a) n
        (KMap (boundedFlatCoefficientOpenRestriction_exact f a) n x) =
      boundedFlatPerfectOpenKRestrict (schemeMap f a) n
        (boundedFlatCoefficientOpenKEquiv f a n x) :=
  boundedFlatCoefficientEvaluationKEquiv_natural (boundedFlatCoefficientOpenWaldhausen f a)
    (boundedFlatPerfectOpenWaldhausen (schemeMap f a))
    (boundedFlatCoefficientSectionEquivalence (op Q, a))
    (boundedFlatCoefficientOpenEvaluation_coarse_exact f a)
    (boundedFlatCoefficientOpenEquivalence_inverse_exact f a)
    (boundedFlatCoefficientSectionWaldhausen (op P, a))
    (boundedFlatPerfectWaldhausen (space (op P, a)))
    (boundedFlatCoefficientSectionEquivalence (op P, a))
    (boundedFlatCoefficientOriginalEvaluation_exact (op P, a))
    (boundedFlatCoefficientSectionEquivalence_inverse_exact (op P, a))
    (boundedFlatCoefficientOpenRestriction_exact f a)
    (boundedFlatPerfectOpenRestriction_exact (schemeMap f a))
    (boundedFlatCoefficientOpenRestrictionEvaluationIso f a) n x

/-- Original native open evaluation followed by the genuine bounded-flat perfect comparison. -/
def boundedFlatCoefficientFullOpenPerfectKEquiv (_f : P ⟶ Q)
    [CompactSpace P.left] (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientSectionWaldhausen (op P, a)).K n ≃*
      (perfectWaldhausen (space (op P, a))).K n := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  exact (boundedFlatCoefficientSectionKEquiv (op P, a) n).trans
    (boundedFlatPerfectKEquiv (space (op P, a)) n)

omit [IsOpenImmersion f.left] in
/-- The perfect evaluation comparison retains the original evaluated object's K-zero class. -/
theorem boundedFlatCoefficientFullOpenPerfectKEquiv_objectClass [CompactSpace P.left]
    (a : Under R) (S : BoundedFlatCoefficientSections (op P, a)) :
    boundedFlatCoefficientFullOpenPerfectKEquiv f a 0
        ((boundedFlatCoefficientSectionWaldhausen (op P, a)).kZeroObjectClass S) =
      (perfectWaldhausen (space (op P, a))).kZeroObjectClass
        ((boundedFlatCoefficientFullOpenPerfectEvaluation f a).obj S) := by
  change boundedFlatPerfectToPerfectKMap (space (op P, a)) 0
    (boundedFlatCoefficientSectionKEquiv (op P, a) 0
      ((boundedFlatCoefficientSectionWaldhausen (op P, a)).kZeroObjectClass S)) = _
  rw [boundedFlatCoefficientSectionKEquiv_objectClass]
  exact KMap_kZeroObjectClass (boundedFlatPerfectInclusion_exact (space (op P, a))) _

/-- Original coarse evaluation followed by the genuine relative-open perfect comparison. -/
def boundedFlatCoefficientOpenPerfectKEquiv [CompactSpace Q.left] (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientOpenWaldhausen f a).K n ≃*
      (perfectOpenWeakWaldhausen (schemeMap f a)).K n := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  exact (boundedFlatCoefficientOpenKEquiv f a n).trans
    (boundedFlatPerfectOpenKEquiv (schemeMap f a) n)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The unchanged original section restriction compares with the original perfect restriction. -/
theorem boundedFlatCoefficientOpenRestriction_perfectKComparison (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientOpenWaldhausen f a).K n) :
    boundedFlatCoefficientFullOpenPerfectKEquiv f a n
        (KMap (boundedFlatCoefficientOpenRestriction_exact f a) n x) =
      perfectOpenKRestrict (schemeMap f a) n
        (boundedFlatCoefficientOpenPerfectKEquiv f a n x) := by
  change boundedFlatPerfectToPerfectKMap (space (op P, a)) n
    (boundedFlatCoefficientSectionKEquiv (op P, a) n
      (KMap (boundedFlatCoefficientOpenRestriction_exact f a) n x)) =
    perfectOpenKRestrict (schemeMap f a) n
      (boundedFlatPerfectOpenToPerfectOpenKMap (schemeMap f a) n
        (boundedFlatCoefficientOpenKEquiv f a n x))
  rw [boundedFlatCoefficientOpenRestriction_KComparison]
  exact (DFunLike.congr_fun
    (boundedFlatPerfectOpenKRestrict_comparison (schemeMap f a) n)
    (boundedFlatCoefficientOpenKEquiv f a n x)).symm

variable [QuasiSeparatedSpace Q.left]

/-- Global cofinality proves original native section restriction injective in every degree. -/
theorem boundedFlatCoefficientOpenRestriction_KMap_injective (a : Under R) (n : ℕ) :
    Function.Injective (KMap (boundedFlatCoefficientOpenRestriction_exact f a) n) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  intro x y hxy
  apply (boundedFlatCoefficientOpenPerfectKEquiv f a n).injective
  apply qcqs_perfectOpenKRestrict_injective (schemeMap f a) n
  rw [← boundedFlatCoefficientOpenRestriction_perfectKComparison f a n x,
    ← boundedFlatCoefficientOpenRestriction_perfectKComparison f a n y, hxy]

/-- The original section restriction is injective on the honest K-zero endpoint. -/
theorem boundedFlatCoefficientOpenRestriction_KMap_zero_injective (a : Under R) :
    Function.Injective (KMap (boundedFlatCoefficientOpenRestriction_exact f a) 0) :=
  boundedFlatCoefficientOpenRestriction_KMap_injective f a 0

/-- Global cofinality proves bijectivity of the same original restriction in positive degrees. -/
theorem boundedFlatCoefficientOpenRestriction_KMap_succ_bijective (a : Under R) (n : ℕ) :
    Function.Bijective (KMap (boundedFlatCoefficientOpenRestriction_exact f a) (n + 1)) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  refine ⟨boundedFlatCoefficientOpenRestriction_KMap_injective f a (n + 1), ?_⟩
  intro y
  obtain ⟨z, hz⟩ := (qcqs_perfectOpenKRestrict_succ_bijective (schemeMap f a) n).surjective
    (boundedFlatCoefficientFullOpenPerfectKEquiv f a (n + 1) y)
  refine ⟨(boundedFlatCoefficientOpenPerfectKEquiv f a (n + 1)).symm z, ?_⟩
  apply (boundedFlatCoefficientFullOpenPerfectKEquiv f a (n + 1)).injective
  rw [boundedFlatCoefficientOpenRestriction_perfectKComparison, MulEquiv.apply_symm_apply]
  exact hz

end Quillen.PerfectComplexes
