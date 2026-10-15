/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionKComparison
public import Quillen.Waldhausen.SConstruction.Iterated.StableKMap
public import Quillen.Waldhausen.SConstruction.Iterated.StableFunctoriality

/-!
# Pointwise spectrum comparison from the actual fine full-open sections

The source is the original direct full-open section Model prespectrum. Evaluation is lifted
through its existing `AsSmall` equivalence, and its actual image zero is canonically rebased
to the target's chosen lifted zero. This gives a genuine Model arrow into the explicitly
lifted bounded-flat original prespectrum of the actual open fiber. Its stable map retains the
original section K-equivalence in every nonnegative degree. Composing with the normalized
original bounded-flat inclusion gives the corresponding perfect map, stable when the open
fiber is quasi-compact. No seed, finite Bass iterate or telescope comparison is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual lifted evaluation image zero has its unique iso to the target's chosen zero. -/
def boundedFlatAffineFullOpenSectionEvaluationZeroIso (a : Under R) :
    (boundedFlatAffineFullOpenSectionSmallEquivalence j a).functor.obj
        (boundedFlatAffineFullOpenSectionWaldhausen j a).zero ≅
      (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel.zero :=
  ((boundedFlatAffineFullOpenSectionSmallEquivalence_exact j a).zero
    (boundedFlatAffineFullOpenSectionWaldhausen j a).isZero).iso
      (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel.isZero

/-- Normalize that original lifted evaluation on the actual direct section Model. -/
def boundedFlatAffineFullOpenSectionEvaluationModelMap (a : Under R) :
    boundedFlatAffineFullOpenSectionModel j a ⟶
      modelOf (boundedFlatPerfectWaldhausen (openSpace j a)) where
  functor := Quillen.rebaseFunctor
    (boundedFlatAffineFullOpenSectionSmallEquivalence j a).functor
    (boundedFlatAffineFullOpenSectionWaldhausen j a).zero
    (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel.zero
    (boundedFlatAffineFullOpenSectionEvaluationZeroIso j a)
  exact := (boundedFlatAffineFullOpenSectionSmallEquivalence_exact j a).rebase
  zero := Quillen.rebaseFunctor_obj_base _ _ _ _

/-- The whole actual normalization retains a natural iso from the original lifted evaluation. -/
def boundedFlatAffineFullOpenSectionEvaluationNormalizationIso (a : Under R) :
    (boundedFlatAffineFullOpenSectionSmallEquivalence j a).functor ≅
      (boundedFlatAffineFullOpenSectionEvaluationModelMap j a).functor :=
  Quillen.rebaseFunctorIso
    (boundedFlatAffineFullOpenSectionSmallEquivalence j a).functor
    (boundedFlatAffineFullOpenSectionWaldhausen j a).zero
    (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel.zero
    (boundedFlatAffineFullOpenSectionEvaluationZeroIso j a)

/-- The normalization sends the original section zero to the specified lifted zero literally. -/
theorem boundedFlatAffineFullOpenSectionEvaluationModelMap_zero (a : Under R) :
    (boundedFlatAffineFullOpenSectionEvaluationModelMap j a).functor.obj
        (boundedFlatAffineFullOpenSectionWaldhausen j a).zero =
      (boundedFlatPerfectWaldhausen (openSpace j a)).smallModel.zero :=
  (boundedFlatAffineFullOpenSectionEvaluationModelMap j a).zero

/-- The genuine map keeps the direct source and the target's explicit common-universe lift. -/
def boundedFlatAffineFullOpenSectionEvaluationPrespectrumMap (a : Under R) :
    (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a ⟶
      originalPrespectrum (boundedFlatPerfectWaldhausen (openSpace j a)) :=
  prespectrumMap (boundedFlatAffineFullOpenSectionEvaluationModelMap j a)

/-- Normalization leaves precisely the original lifted evaluation K-map after universe lifting. -/
theorem boundedFlatAffineFullOpenSectionEvaluationModelMap_KMap
    (a : Under R) (n : ℕ)
    (x : (boundedFlatAffineFullOpenSectionWaldhausen j a).K n) :
    KMap (boundedFlatAffineFullOpenSectionEvaluationModelMap j a).exact n x =
      (boundedFlatPerfectWaldhausen (openSpace j a)).smallModelKEquiv n
        (boundedFlatAffineFullOpenSectionKEquiv j a n x) := by
  change KMap (boundedFlatAffineFullOpenSectionSmallEquivalence_exact j a).rebase n x = _
  rw [boundedFlatAffineFullOpenSectionKEquiv_apply, MulEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun
    (KMap_eq_of_iso (boundedFlatAffineFullOpenSectionSmallEquivalence_exact j a)
      (boundedFlatAffineFullOpenSectionSmallEquivalence_exact j a).rebase
      (boundedFlatAffineFullOpenSectionEvaluationNormalizationIso j a) n) x).symm

/-- The original section K-equivalence is the actual nonnegative stable map of evaluation. -/
theorem boundedFlatAffineFullOpenSectionEvaluationPrespectrumMap_KEquiv
    (a : Under R) (n : ℕ)
    (x : (boundedFlatAffineFullOpenSectionWaldhausen j a).K n) :
    originalKStableEquiv (boundedFlatPerfectWaldhausen (openSpace j a)) n
        (Additive.ofMul (boundedFlatAffineFullOpenSectionKEquiv j a n x)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedFlatAffineFullOpenSectionEvaluationPrespectrumMap j a)
        (levelOneStableEquiv (prespectrum (boundedFlatAffineFullOpenSectionModel j a))
          (prespectrum_isOmega (boundedFlatAffineFullOpenSectionModel j a)) n
          (Additive.ofMul x)) := by
  change levelOneStableEquiv
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen (openSpace j a))))
      (prespectrum_isOmega _) n
      (Additive.ofMul ((boundedFlatPerfectWaldhausen (openSpace j a)).smallModelKEquiv n
        (boundedFlatAffineFullOpenSectionKEquiv j a n x))) = _
  rw [← boundedFlatAffineFullOpenSectionEvaluationModelMap_KMap]
  exact prespectrumMap_KMap_stable_naturality
    (boundedFlatAffineFullOpenSectionEvaluationModelMap j a) n x

/-- This actual evaluation arrow is stable in every signed degree without compactness. -/
theorem boundedFlatAffineFullOpenSectionEvaluationPrespectrumMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence (boundedFlatAffineFullOpenSectionEvaluationPrespectrumMap j a) := by
  change IsStableEquivalence
    (prespectrumMap (boundedFlatAffineFullOpenSectionEvaluationModelMap j a))
  have hK (n : ℕ) : Function.Bijective
      (KMap (boundedFlatAffineFullOpenSectionEvaluationModelMap j a).exact n) := by
    have he :
        (fun x ↦ KMap (boundedFlatAffineFullOpenSectionEvaluationModelMap j a).exact n x) =
        (fun x ↦ (boundedFlatPerfectWaldhausen (openSpace j a)).smallModelKEquiv n
          (boundedFlatAffineFullOpenSectionKEquiv j a n x)) := by
      funext x
      exact boundedFlatAffineFullOpenSectionEvaluationModelMap_KMap j a n x
    change Function.Bijective (fun x ↦
      KMap (boundedFlatAffineFullOpenSectionEvaluationModelMap j a).exact n x)
    rw [he]
    exact ((boundedFlatPerfectWaldhausen (openSpace j a)).smallModelKEquiv n).bijective.comp
      (boundedFlatAffineFullOpenSectionKEquiv j a n).bijective
  intro d
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  by_cases hd : d < 0
  · let : Subsingleton ((stableHomotopyFunctor d).obj
        (prespectrum (boundedFlatAffineFullOpenSectionModel j a))) :=
      prespectrum_stableHomotopyGroup_neg_subsingleton
        (boundedFlatAffineFullOpenSectionModel j a) d hd
    let : Subsingleton ((stableHomotopyFunctor d).obj
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen (openSpace j a))))) :=
      prespectrum_stableHomotopyGroup_neg_subsingleton
        (modelOf (boundedFlatPerfectWaldhausen (openSpace j a))) d hd
    exact Function.bijective_of_subsingleton' _
  · have he : d = (d.toNat : ℤ) := by omega
    rw [he]
    exact ⟨prespectrumMap_stable_nonnegative_injective
      (boundedFlatAffineFullOpenSectionEvaluationModelMap j a) d.toNat (hK d.toNat).1,
      prespectrumMap_stable_nonnegative_surjective
        (boundedFlatAffineFullOpenSectionEvaluationModelMap j a) d.toNat (hK d.toNat).2⟩

/-- Compose with the original normalized bounded-flat inclusion into the lifted perfect spectrum. -/
def boundedFlatAffineFullOpenSectionPerfectEvaluationPrespectrumMap (a : Under R) :
    (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a ⟶
      originalPrespectrum (perfectWaldhausen (openSpace j a)) :=
  boundedFlatAffineFullOpenSectionEvaluationPrespectrumMap j a ≫
    exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (openSpace j a))
      (perfectWaldhausen (openSpace j a)) (boundedFlatPerfectInclusion_exact (openSpace j a))

/-- The perfect stable map retains the literal original inclusion K-map after evaluation. -/
theorem boundedFlatAffineFullOpenSectionPerfectEvaluationPrespectrumMap_KMap
    (a : Under R) (n : ℕ)
    (x : (boundedFlatAffineFullOpenSectionWaldhausen j a).K n) :
    originalKStableEquiv (perfectWaldhausen (openSpace j a)) n
        (Additive.ofMul (boundedFlatPerfectToPerfectKMap (openSpace j a) n
          (boundedFlatAffineFullOpenSectionKEquiv j a n x))) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedFlatAffineFullOpenSectionPerfectEvaluationPrespectrumMap j a)
        (levelOneStableEquiv (prespectrum (boundedFlatAffineFullOpenSectionModel j a))
          (prespectrum_isOmega (boundedFlatAffineFullOpenSectionModel j a)) n
          (Additive.ofMul x)) := by
  have h := originalKStableEquiv_exact_naturality
    (boundedFlatPerfectWaldhausen (openSpace j a)) (perfectWaldhausen (openSpace j a))
    (boundedFlatPerfectInclusion_exact (openSpace j a)) n
    (boundedFlatAffineFullOpenSectionKEquiv j a n x)
  rw [boundedFlatAffineFullOpenSectionEvaluationPrespectrumMap_KEquiv] at h
  exact h.trans (by rw [boundedFlatAffineFullOpenSectionPerfectEvaluationPrespectrumMap,
    Functor.map_comp]; rfl)

variable [CompactSpace U]

/-- Compactness is used only to make the original perfect inclusion a stable equivalence. -/
theorem boundedFlatAffineFullOpenSectionPerfectEvaluationPrespectrumMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence
      (boundedFlatAffineFullOpenSectionPerfectEvaluationPrespectrumMap j a) := by
  let : CompactSpace (openSpace j a) := compactSpace_openSpace j a
  apply IsStableEquivalence.comp
    (boundedFlatAffineFullOpenSectionEvaluationPrespectrumMap_isStableEquivalence j a)
  apply (exactOriginalPrespectrumMap_isStableEquivalence_iff
    (boundedFlatPerfectWaldhausen (openSpace j a)) (perfectWaldhausen (openSpace j a))
    (boundedFlatPerfectInclusion_exact (openSpace j a))).mpr
  exact boundedFlatPerfectToPerfectKMap_bijective (openSpace j a)

/-- Under compactness the same actual perfect map is the existing section perfect K-equivalence. -/
theorem boundedFlatAffineFullOpenSectionPerfectEvaluationPrespectrumMap_KEquiv
    (a : Under R) (n : ℕ)
    (x : (boundedFlatAffineFullOpenSectionWaldhausen j a).K n) :
    originalKStableEquiv (perfectWaldhausen (openSpace j a)) n
        (Additive.ofMul (boundedFlatAffineFullOpenSectionPerfectKEquiv j a n x)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedFlatAffineFullOpenSectionPerfectEvaluationPrespectrumMap j a)
        (levelOneStableEquiv (prespectrum (boundedFlatAffineFullOpenSectionModel j a))
          (prespectrum_isOmega (boundedFlatAffineFullOpenSectionModel j a)) n
          (Additive.ofMul x)) := by
  rw [boundedFlatAffineFullOpenSectionPerfectKEquiv_apply]
  exact boundedFlatAffineFullOpenSectionPerfectEvaluationPrespectrumMap_KMap j a n x

end Quillen.PerfectComplexes
