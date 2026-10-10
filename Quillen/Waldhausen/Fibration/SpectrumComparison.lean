/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Fibration.Prespectrum
public import Quillen.Topology.Prespectrum.FiberOmega
public import Quillen.Waldhausen.SConstruction.Iterated.HomotopyTransport
public import Quillen.Topology.Prespectrum.StableLevelOne
public import Quillen.Topology.Prespectrum.FiberConnectivity
public import Quillen.Topology.Prespectrum.StableEquivalence
public import Quillen.Waldhausen.Fibration.GeneralComparison
public import Quillen.Waldhausen.Fibration.LongExactSequence
public import Quillen.Waldhausen.SConstruction.Iterated.StableHomotopy
public import Quillen.Topology.Prespectrum.FiberSequence

/-!
The specified original acyclic comparison is an all-integer stable equivalence of the actual
S-spectra under the structural Waldhausen fibration hypotheses. This is a connective spectrum
theorem, not a Bass nonconnective construction.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Quillen.Waldhausen.Fibration
open IteratedS LoopPrespectrum
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The homeomorphism between the original based fiber and the prespectrum fiber at level one. -/
def originalFiberToSpectrumLevelOne :
    HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint ≃ₜ
      (homotopyFiber (changeWeakPrespectrumMap N)).space 1 :=
  (HomotopyFiber.homeomorphOfSquare (changeWeakMap N)
    ((changeWeakPrespectrumMap N).map 1)
    V.smallModelDeloopingHomeomorph N.coarse.smallModelDeloopingHomeomorph
    (smallModelDeloopingHomeomorph_naturality (changeWeak_exact N))
    N.coarse.kBasepoint).trans
      (HomotopyFiber.congrHomeomorph rfl N.coarse.smallModelDeloopingHomeomorph_basepoint)

theorem acyclicPrespectrumNullhomotopy_level_one (t : unitInterval)
    (x : (acyclicStructure N).Delooping) :
    (acyclicPrespectrumNullhomotopy N).level 1
      (t,(acyclicStructure N).smallModelDeloopingHomeomorph x) =
      N.coarse.smallModelDeloopingHomeomorph (acyclicNullhomotopy N (t,x)) := by
  exact originalPrespectrumTransformationHomotopy_level_one
    (acyclicStructure N) N.coarse (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
    (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N)
    rfl (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm) (unitInterval.symm t) x

/-- The whole original canonical fiber map, including its actual path, is exactly
level one of the constructed spectrum map after the specified homeomorphisms. -/
theorem canonicalFiberPrespectrumMap_level_one_square :
    (originalFiberToSpectrumLevelOne N).toHomotopyEquiv.toFun.comp (canonicalFiberMap N) =
      ((canonicalFiberPrespectrumMap N).map 1).comp
        (acyclicStructure N).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact ContinuousMap.congr_fun
      (smallModelDeloopingHomeomorph_naturality (acyclicInclusion_exact N)) x
  · apply ContinuousMap.ext
    intro t
    exact (acyclicPrespectrumNullhomotopy_level_one N t x).symm

/-- Weakness of the actual original comparison passes to the unchanged level-one map. -/
theorem canonicalFiberPrespectrumMap_level_one_weak
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) :
    IsWeakHomotopyEquivalence ((canonicalFiberPrespectrumMap N).map 1) := by
  have hh := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (originalFiberToSpectrumLevelOne N).toHomotopyEquiv).comp h
  rw [canonicalFiberPrespectrumMap_level_one_square] at hh
  exact hh.of_comp_left (isWeakHomotopyEquivalence_of_homotopyEquiv
    (acyclicStructure N).smallModelDeloopingHomeomorph.toHomotopyEquiv)

/-- The nonnegative stable comparison follows from the actual level-one weak theorem. -/
theorem canonicalFiberPrespectrumMap_nonneg_isIso
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map (canonicalFiberPrespectrumMap N)) := by
  apply stableMap_nonneg_isIso_of_levelOne
    (originalPrespectrum_isOmega (acyclicStructure N))
    (homotopyFiber_isOmega _ (originalPrespectrum_isOmega V) (originalPrespectrum_isOmega N.coarse))
  have hh := canonicalFiberPrespectrumMap_level_one_weak N h
  have hb {y : (homotopyFiber (changeWeakPrespectrumMap N)).space 1}
      (e : (canonicalFiberPrespectrumMap N).map 1
        ((originalPrespectrum (acyclicStructure N)).point 1) = y) :
      Function.Bijective (homotopyGroupMap (N := Fin (n+1))
        ((canonicalFiberPrespectrumMap N).map 1) e) := by
    cases e
    exact hh.homotopy_bijective _ _
  exact hb ((canonicalFiberPrespectrumMap N).map_point 1)

/-- The original change-of-weakness map is surjective on the actual stable K0
term whenever its original canonical comparison is weak. -/
theorem changeWeakPrespectrumMap_zero_surjective
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) :
    Function.Surjective ((stableHomotopyFunctor 0).map (changeWeakPrespectrumMap N)) := by
  intro y
  obtain ⟨a,ha⟩ := changeWeak_KMap_zero_surjective_of_weak N h
    ((originalKStableEquiv N.coarse 0).symm y).toMul
  refine ⟨originalKStableEquiv V 0 (Additive.ofMul a), ?_⟩
  change (stableHomotopyFunctor (0 : ℤ)).map
    (originalPrespectrumMap V N.coarse (changeWeak_exact N) N.zero_eq.symm)
    (originalKStableEquiv V 0 (Additive.ofMul a)) = y
  exact (originalKStableEquiv_naturality V N.coarse (changeWeak_exact N) N.zero_eq.symm 0
    a).symm.trans
    ((congrArg (fun b ↦ originalKStableEquiv N.coarse 0 (Additive.ofMul b)) ha).trans
      ((originalKStableEquiv N.coarse 0).apply_symm_apply y))

/-- The actual target fiber is connective; negative-one vanishing uses the
proved original K0 surjectivity rather than being assumed. -/
theorem changeWeakPrespectrumFiber_neg_subsingleton
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (d : ℤ) (hd : d < 0) :
    Subsingleton (stableHomotopyGroup (homotopyFiber (changeWeakPrespectrumMap N)) d) :=
  stableFiber_neg_subsingleton_of_connective _
    (originalStableHomotopyGroup_neg_subsingleton V)
    (originalStableHomotopyGroup_neg_subsingleton N.coarse)
    (changeWeakPrespectrumMap_zero_surjective N h) d hd

/-- The actual coherent acyclic comparison is a stable equivalence in every
integer degree, retaining its specified original nullhomotopy. -/
theorem canonicalFiberPrespectrumMap_isStableEquivalence_of_weak
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) :
    IsStableEquivalence (canonicalFiberPrespectrumMap N) := by
  intro d
  by_cases hd : 0 ≤ d
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hd
    exact canonicalFiberPrespectrumMap_nonneg_isIso N h n
  · have hs := originalStableHomotopyGroup_neg_subsingleton (acyclicStructure N) d (by omega)
    have ht := changeWeakPrespectrumFiber_neg_subsingleton N h d (by omega)
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨fun _ _ _ ↦ hs.elim _ _, fun y ↦ ⟨0,ht.elim _ _⟩⟩

/-- The structural Waldhausen fibration theorem now holds for the actual
constructed S-spectra, with independent object and morphism universes. -/
theorem canonicalFiberPrespectrumMap_isStableEquivalence_general
    [N.coarse.weq.HasTwoOutOfThreeProperty]
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D) :
    IsStableEquivalence (canonicalFiberPrespectrumMap N) :=
  canonicalFiberPrespectrumMap_isStableEquivalence_of_weak N
    (canonicalFiberMap_isWeakHomotopyEquivalence_general N he D hs)

end Quillen.Waldhausen.Fibration
