/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalCofinality
public import Quillen.Waldhausen.SConstruction.Iterated.StableFunctoriality
public import Quillen.Waldhausen.SConstruction.Iterated.ConeStableSequence

/-!
# The original coarse-to-full-open connective deficit

The actual exact restriction from the relative-open perfect model to perfect complexes on the
open defines an unchanged original prespectrum map and its literal mapping cone. For qcqs X
and quasi-compact U, genuine cofinality and original stable cone excision show that this cone
has no signed stable homotopy outside degree zero. No stable equivalence of the restriction,
Bass transition vanishing, or full-open telescope comparison is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The exact original restriction from the coarse model to all perfect complexes on the open. -/
def perfectOpenRestrictPrespectrumMap :
    originalPrespectrum (perfectOpenWeakWaldhausen j) ⟶
      originalPrespectrum (perfectWaldhausen U) :=
  exactOriginalPrespectrumMap (perfectOpenWeakWaldhausen j) (perfectWaldhausen U)
    (perfectOpenRestrict_waldhausenExact j)

/-- The deficit is the actual original mapping cone, with its original face and cylinder. -/
def perfectOpenDeficit : LoopPrespectrum := mappingCone (perfectOpenRestrictPrespectrumMap j)

/-- Actual S-model growth and point HEP discharge the original deficit's stable excision. -/
theorem perfectOpenRestrictPrespectrumMap_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison (perfectOpenRestrictPrespectrumMap j)) :=
  originalPrespectrum_mappingConeFiberComparison_isStableEquivalence
    (perfectOpenWeakWaldhausen j) (perfectWaldhausen U) (perfectOpenRestrictPrespectrumMap j)

/-- The original nonnegative stable map retains the unchanged relative restriction K-map. -/
theorem perfectOpenRestrictPrespectrumMap_stable_naturality (n : ℕ) (a : PerfectOpenK j n) :
    (stableHomotopyFunctor (n : ℤ)).map (perfectOpenRestrictPrespectrumMap j)
        (originalKStableEquiv (perfectOpenWeakWaldhausen j) n (Additive.ofMul a)) =
      originalKStableEquiv (perfectWaldhausen U) n
        (Additive.ofMul (perfectOpenKRestrict j n a)) :=
  (originalKStableEquiv_exact_naturality (perfectOpenWeakWaldhausen j)
    (perfectWaldhausen U) (perfectOpenRestrict_waldhausenExact j) n a).symm

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]

/-- Genuine qcqs cofinality makes the unchanged stable restriction injective in every degree. -/
theorem perfectOpenRestrictPrespectrumMap_stable_injective (d : ℤ) :
    Function.Injective ((stableHomotopyFunctor d).map (perfectOpenRestrictPrespectrumMap j)) := by
  by_cases hd : d < 0
  · intro a b _
    exact (originalStableHomotopyGroup_neg_subsingleton
      (perfectOpenWeakWaldhausen j) d hd).elim a b
  · have he : d = (d.toNat : ℤ) := by omega
    rw [he]
    intro x y hxy
    obtain ⟨a, rfl⟩ := (originalKStableEquiv (perfectOpenWeakWaldhausen j) d.toNat).surjective x
    obtain ⟨b, rfl⟩ := (originalKStableEquiv (perfectOpenWeakWaldhausen j) d.toNat).surjective y
    have h := (perfectOpenRestrictPrespectrumMap_stable_naturality j d.toNat a.toMul).symm.trans
      (hxy.trans (perfectOpenRestrictPrespectrumMap_stable_naturality j d.toNat b.toMul))
    have hab := qcqs_perfectOpenKRestrict_injective j d.toNat
      (congrArg Additive.toMul ((originalKStableEquiv (perfectWaldhausen U) d.toNat).injective h))
    exact congrArg (originalKStableEquiv (perfectOpenWeakWaldhausen j) d.toNat)
      (congrArg Additive.ofMul hab)

/-- The same original stable restriction is surjective away from the honest degree-zero image. -/
theorem perfectOpenRestrictPrespectrumMap_stable_surjective_of_ne_zero
    (d : ℤ) (hd : d ≠ 0) :
    Function.Surjective ((stableHomotopyFunctor d).map (perfectOpenRestrictPrespectrumMap j)) := by
  by_cases hn : d < 0
  · intro x
    exact ⟨0, (originalStableHomotopyGroup_neg_subsingleton
      (perfectWaldhausen U) d hn).elim _ _⟩
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    have hk : Function.Bijective (perfectOpenKRestrict j d.toNat) := by
      rw [hp]
      exact qcqs_perfectOpenKRestrict_succ_bijective j (d.toNat - 1)
    rw [he]
    exact ((exactStableKMap_nonnegative_bijective_iff
      (perfectOpenWeakWaldhausen j) (perfectWaldhausen U)
      (perfectOpenRestrict_waldhausenExact j) d.toNat).mpr hk).surjective

/-- The original deficit has signed stable homotopy only in degree zero. The degree-one case
uses genuine injectivity of the original K-zero restriction. -/
theorem perfectOpenDeficit_stableHomotopyGroup_subsingleton (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (stableHomotopyGroup (perfectOpenDeficit j) d) := by
  let f := perfectOpenRestrictPrespectrumMap j
  let hf := perfectOpenRestrictPrespectrumMap_coneFiber_isStableEquivalence j
  have hs : Function.Surjective ((stableHomotopyFunctor (d - 1 + 1)).map f) :=
    perfectOpenRestrictPrespectrumMap_stable_surjective_of_ne_zero j (d - 1 + 1) (by omega)
  have hi := perfectOpenRestrictPrespectrumMap_stable_injective j (d - 1)
  have hzero : ∀ x : stableHomotopyGroup (mappingCone f) (d - 1 + 1), x = 0 := by
    intro x
    have hb : stableMappingConeConnecting f hf (d - 1) x = 0 :=
      hi (((stableMappingConeConnecting_exact_source f hf (d - 1) _).mpr ⟨x, rfl⟩).trans
        (map_zero ((stableHomotopyFunctor (d - 1)).map f).hom).symm)
    obtain ⟨y, hy⟩ := (stableMappingConeConnecting_exact_cone f hf (d - 1) x).mp hb
    obtain ⟨z, rfl⟩ := hs y
    exact hy.symm.trans ((stableMappingCone_exact_target f hf (d - 1 + 1) _).mpr ⟨z, rfl⟩)
  have hz : Subsingleton (stableHomotopyGroup (mappingCone f) (d - 1 + 1)) :=
    ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
  change Subsingleton (stableHomotopyGroup (mappingCone f) d)
  exact Eq.mp (congrArg (fun k : ℤ ↦ Subsingleton (stableHomotopyGroup (mappingCone f) k))
    (sub_add_cancel d 1)) hz

end Quillen.PerfectComplexes
