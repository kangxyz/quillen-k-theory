/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionKComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.KComparison
public import Quillen.Waldhausen.SConstruction.Iterated.StableKMap
public import Quillen.Waldhausen.SConstruction.Iterated.StableFunctoriality

/-!
# Pointwise spectrum evaluation of the original native coefficient sections

Every joint fiber uses its original fine section Model and the one joint zero.
Original identity evaluation is lifted by the common-universe `AsSmall` equivalence,
then canonically rebased to the chosen lifted bounded-flat zero. The resulting actual
prespectrum arrow retains the original forward K-equations, including degree zero.
The bounded-flat map is stable in every signed degree without compactness; the original
perfect inclusion is stable when the specified scheme over the base is quasi-compact.
Naturality and actual geometric comparison tracks are supplied separately.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}

/-- Original identity evaluation lifted through the existing common-universe equivalence. -/
def boundedFlatCoefficientSectionSmallEquivalence (i : Index R) :
    BoundedFlatCoefficientSections i ≌ SmallModel (BoundedFlatPerfect (space i)) :=
  (boundedFlatCoefficientSectionEquivalence i).trans AsSmall.equiv

/-- The actual lifted evaluation preserves the original transported section classes. -/
theorem boundedFlatCoefficientSectionSmallEquivalence_exact (i : Index R) :
    IsExact (boundedFlatCoefficientSectionWaldhausen i).cof
      (boundedFlatCoefficientSectionWaldhausen i).weq
      (boundedFlatPerfectWaldhausen (space i)).smallModel.cof
      (boundedFlatPerfectWaldhausen (space i)).smallModel.weq
      (boundedFlatCoefficientSectionSmallEquivalence i).functor :=
  (boundedFlatCoefficientOriginalEvaluation_exact i).comp
    (boundedFlatPerfectWaldhausen (space i)).smallModel_up_exact

/-- The inverse lowers only the universe before applying the actual evaluation inverse. -/
theorem boundedFlatCoefficientSectionSmallEquivalence_inverse_exact (i : Index R) :
    IsExact (boundedFlatPerfectWaldhausen (space i)).smallModel.cof
      (boundedFlatPerfectWaldhausen (space i)).smallModel.weq
      (boundedFlatCoefficientSectionWaldhausen i).cof
      (boundedFlatCoefficientSectionWaldhausen i).weq
      (boundedFlatCoefficientSectionSmallEquivalence i).inverse :=
  (boundedFlatPerfectWaldhausen (space i)).smallModel_down_exact.comp
    (boundedFlatCoefficientSectionEquivalence_inverse_exact i)

/-- The forward map is the original lifted evaluation K-map, then universe lowering. -/
theorem boundedFlatCoefficientSectionKEquiv_apply (i : Index R) (n : ℕ)
    (x : (boundedFlatCoefficientSectionWaldhausen i).K n) :
    boundedFlatCoefficientSectionKEquiv i n x =
      ((boundedFlatPerfectWaldhausen (space i)).smallModelKEquiv n).symm
        (KMap (boundedFlatCoefficientSectionSmallEquivalence_exact i) n x) := rfl

/-- Evaluation followed by the unchanged original bounded-flat inclusion on a compact fiber. -/
def boundedFlatCoefficientSectionPerfectKEquiv (i : Index R)
    [CompactSpace i.1.unop.left] (n : ℕ) :
    (boundedFlatCoefficientSectionWaldhausen i).K n ≃*
      (perfectWaldhausen (space i)).K n := by
  letI : CompactSpace (space i) := compactSpace_space i
  exact (boundedFlatCoefficientSectionKEquiv i n).trans (boundedFlatPerfectKEquiv (space i) n)

/-- The perfect forward map is precisely the original inclusion after identity evaluation. -/
theorem boundedFlatCoefficientSectionPerfectKEquiv_apply (i : Index R)
    [CompactSpace i.1.unop.left] (n : ℕ)
    (x : (boundedFlatCoefficientSectionWaldhausen i).K n) :
    boundedFlatCoefficientSectionPerfectKEquiv i n x =
      boundedFlatPerfectToPerfectKMap (space i) n
        (boundedFlatCoefficientSectionKEquiv i n x) := rfl

/-- The actual lifted evaluation image zero has its unique iso to the target's chosen zero. -/
def boundedFlatCoefficientSectionEvaluationZeroIso (i : Index R) :
    (boundedFlatCoefficientSectionSmallEquivalence i).functor.obj
        (boundedFlatCoefficientSectionWaldhausen i).zero ≅
      (boundedFlatPerfectWaldhausen (space i)).smallModel.zero :=
  ((boundedFlatCoefficientSectionSmallEquivalence_exact i).zero
    (boundedFlatCoefficientSectionWaldhausen i).isZero).iso
      (boundedFlatPerfectWaldhausen (space i)).smallModel.isZero

/-- Normalize that original lifted evaluation on the actual direct section Model. -/
def boundedFlatCoefficientSectionEvaluationModelMap (i : Index R) :
    boundedFlatCoefficientSectionModel i ⟶
      modelOf (boundedFlatPerfectWaldhausen (space i)) where
  functor := Quillen.rebaseFunctor
    (boundedFlatCoefficientSectionSmallEquivalence i).functor
    (boundedFlatCoefficientSectionWaldhausen i).zero
    (boundedFlatPerfectWaldhausen (space i)).smallModel.zero
    (boundedFlatCoefficientSectionEvaluationZeroIso i)
  exact := (boundedFlatCoefficientSectionSmallEquivalence_exact i).rebase
  zero := Quillen.rebaseFunctor_obj_base _ _ _ _

/-- The whole actual normalization retains a natural iso from the original lifted evaluation. -/
def boundedFlatCoefficientSectionEvaluationNormalizationIso (i : Index R) :
    (boundedFlatCoefficientSectionSmallEquivalence i).functor ≅
      (boundedFlatCoefficientSectionEvaluationModelMap i).functor :=
  Quillen.rebaseFunctorIso
    (boundedFlatCoefficientSectionSmallEquivalence i).functor
    (boundedFlatCoefficientSectionWaldhausen i).zero
    (boundedFlatPerfectWaldhausen (space i)).smallModel.zero
    (boundedFlatCoefficientSectionEvaluationZeroIso i)

/-- The normalization sends the original section zero to the specified lifted zero literally. -/
theorem boundedFlatCoefficientSectionEvaluationModelMap_zero (i : Index R) :
    (boundedFlatCoefficientSectionEvaluationModelMap i).functor.obj
        (boundedFlatCoefficientSectionWaldhausen i).zero =
      (boundedFlatPerfectWaldhausen (space i)).smallModel.zero :=
  (boundedFlatCoefficientSectionEvaluationModelMap i).zero

/-- The genuine map keeps the direct source and the target's explicit common-universe lift. -/
def boundedFlatCoefficientSectionEvaluationPrespectrumMap (i : Index R) :
    (boundedFlatCoefficientSectionPrespectrumFunctor R).obj i ⟶
      originalPrespectrum (boundedFlatPerfectWaldhausen (space i)) :=
  prespectrumMap (boundedFlatCoefficientSectionEvaluationModelMap i)

/-- Normalization leaves precisely the original lifted evaluation K-map after universe lifting. -/
theorem boundedFlatCoefficientSectionEvaluationModelMap_KMap
    (i : Index R) (n : ℕ)
    (x : (boundedFlatCoefficientSectionWaldhausen i).K n) :
    KMap (boundedFlatCoefficientSectionEvaluationModelMap i).exact n x =
      (boundedFlatPerfectWaldhausen (space i)).smallModelKEquiv n
        (boundedFlatCoefficientSectionKEquiv i n x) := by
  change KMap (boundedFlatCoefficientSectionSmallEquivalence_exact i).rebase n x = _
  rw [boundedFlatCoefficientSectionKEquiv_apply, MulEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun
    (KMap_eq_of_iso (boundedFlatCoefficientSectionSmallEquivalence_exact i)
      (boundedFlatCoefficientSectionSmallEquivalence_exact i).rebase
      (boundedFlatCoefficientSectionEvaluationNormalizationIso i) n) x).symm

/-- The original section K-equivalence is the actual nonnegative stable map of evaluation. -/
theorem boundedFlatCoefficientSectionEvaluationPrespectrumMap_KEquiv
    (i : Index R) (n : ℕ)
    (x : (boundedFlatCoefficientSectionWaldhausen i).K n) :
    originalKStableEquiv (boundedFlatPerfectWaldhausen (space i)) n
        (Additive.ofMul (boundedFlatCoefficientSectionKEquiv i n x)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedFlatCoefficientSectionEvaluationPrespectrumMap i)
        (levelOneStableEquiv (prespectrum (boundedFlatCoefficientSectionModel i))
          (prespectrum_isOmega (boundedFlatCoefficientSectionModel i)) n
          (Additive.ofMul x)) := by
  change levelOneStableEquiv
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space i))))
      (prespectrum_isOmega _) n
      (Additive.ofMul ((boundedFlatPerfectWaldhausen (space i)).smallModelKEquiv n
        (boundedFlatCoefficientSectionKEquiv i n x))) = _
  rw [← boundedFlatCoefficientSectionEvaluationModelMap_KMap]
  exact prespectrumMap_KMap_stable_naturality
    (boundedFlatCoefficientSectionEvaluationModelMap i) n x

/-- This actual evaluation arrow is stable in every signed degree without compactness. -/
theorem boundedFlatCoefficientSectionEvaluationPrespectrumMap_isStableEquivalence
    (i : Index R) :
    IsStableEquivalence (boundedFlatCoefficientSectionEvaluationPrespectrumMap i) := by
  change IsStableEquivalence
    (prespectrumMap (boundedFlatCoefficientSectionEvaluationModelMap i))
  have hK (n : ℕ) : Function.Bijective
      (KMap (boundedFlatCoefficientSectionEvaluationModelMap i).exact n) := by
    have he :
        (fun x ↦ KMap (boundedFlatCoefficientSectionEvaluationModelMap i).exact n x) =
        (fun x ↦ (boundedFlatPerfectWaldhausen (space i)).smallModelKEquiv n
          (boundedFlatCoefficientSectionKEquiv i n x)) := by
      funext x
      exact boundedFlatCoefficientSectionEvaluationModelMap_KMap i n x
    change Function.Bijective (fun x ↦
      KMap (boundedFlatCoefficientSectionEvaluationModelMap i).exact n x)
    rw [he]
    exact ((boundedFlatPerfectWaldhausen (space i)).smallModelKEquiv n).bijective.comp
      (boundedFlatCoefficientSectionKEquiv i n).bijective
  intro d
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  by_cases hd : d < 0
  · let : Subsingleton ((stableHomotopyFunctor d).obj
        (prespectrum (boundedFlatCoefficientSectionModel i))) :=
      prespectrum_stableHomotopyGroup_neg_subsingleton
        (boundedFlatCoefficientSectionModel i) d hd
    let : Subsingleton ((stableHomotopyFunctor d).obj
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space i))))) :=
      prespectrum_stableHomotopyGroup_neg_subsingleton
        (modelOf (boundedFlatPerfectWaldhausen (space i))) d hd
    exact Function.bijective_of_subsingleton' _
  · have he : d = (d.toNat : ℤ) := by omega
    rw [he]
    exact ⟨prespectrumMap_stable_nonnegative_injective
      (boundedFlatCoefficientSectionEvaluationModelMap i) d.toNat (hK d.toNat).1,
      prespectrumMap_stable_nonnegative_surjective
        (boundedFlatCoefficientSectionEvaluationModelMap i) d.toNat (hK d.toNat).2⟩

/-- Compose with the original normalized bounded-flat inclusion into the lifted perfect spectrum. -/
def boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap (i : Index R) :
    (boundedFlatCoefficientSectionPrespectrumFunctor R).obj i ⟶
      originalPrespectrum (perfectWaldhausen (space i)) :=
  boundedFlatCoefficientSectionEvaluationPrespectrumMap i ≫
    exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (space i))
      (perfectWaldhausen (space i)) (boundedFlatPerfectInclusion_exact (space i))

/-- The perfect stable map retains the literal original inclusion K-map after evaluation. -/
theorem boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KMap
    (i : Index R) (n : ℕ)
    (x : (boundedFlatCoefficientSectionWaldhausen i).K n) :
    originalKStableEquiv (perfectWaldhausen (space i)) n
        (Additive.ofMul (boundedFlatPerfectToPerfectKMap (space i) n
          (boundedFlatCoefficientSectionKEquiv i n x))) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap i)
        (levelOneStableEquiv (prespectrum (boundedFlatCoefficientSectionModel i))
          (prespectrum_isOmega (boundedFlatCoefficientSectionModel i)) n
          (Additive.ofMul x)) := by
  have h := originalKStableEquiv_exact_naturality
    (boundedFlatPerfectWaldhausen (space i)) (perfectWaldhausen (space i))
    (boundedFlatPerfectInclusion_exact (space i)) n
    (boundedFlatCoefficientSectionKEquiv i n x)
  rw [boundedFlatCoefficientSectionEvaluationPrespectrumMap_KEquiv] at h
  exact h.trans (by rw [boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap,
    Functor.map_comp]; rfl)


/-- Compactness is used only to make the original perfect inclusion a stable equivalence. -/
theorem boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap_isStableEquivalence
    (i : Index R) [CompactSpace i.1.unop.left] :
    IsStableEquivalence
      (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap i) := by
  let : CompactSpace (space i) := compactSpace_space i
  apply IsStableEquivalence.comp
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap_isStableEquivalence i)
  apply (exactOriginalPrespectrumMap_isStableEquivalence_iff
    (boundedFlatPerfectWaldhausen (space i)) (perfectWaldhausen (space i))
    (boundedFlatPerfectInclusion_exact (space i))).mpr
  exact boundedFlatPerfectToPerfectKMap_bijective (space i)

/-- Under compactness the same actual perfect map is the existing section perfect K-equivalence. -/
theorem boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KEquiv
    (i : Index R) [CompactSpace i.1.unop.left] (n : ℕ)
    (x : (boundedFlatCoefficientSectionWaldhausen i).K n) :
    originalKStableEquiv (perfectWaldhausen (space i)) n
        (Additive.ofMul (boundedFlatCoefficientSectionPerfectKEquiv i n x)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap i)
        (levelOneStableEquiv (prespectrum (boundedFlatCoefficientSectionModel i))
          (prespectrum_isOmega (boundedFlatCoefficientSectionModel i)) n
          (Additive.ofMul x)) := by
  rw [boundedFlatCoefficientSectionPerfectKEquiv_apply]
  exact boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KMap i n x

end Quillen.PerfectComplexes
