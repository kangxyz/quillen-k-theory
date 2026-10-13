/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionKZeroExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionGradingPrespectrum
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionCofinality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenGradedSectionStable
public import Quillen.Waldhausen.SConstruction.Iterated.StableKMap
public import Quillen.Waldhausen.SConstruction.Iterated.ConeFiberExcision
public import Quillen.Topology.Prespectrum.ConeDescZeroComparison

/-!
# The actual full-open section restriction cone and original quotient grading

For any specified null of the actual restriction followed by the original grading map,
the unchanged cone descent is stable in every integer degree. The original section K-zero
image/kernel theorem and grading surjectivity give the honest degree-zero cokernel. Original
positive cofinality, K-zero injectivity and Model connectivity concentrate its actual cone in
degree zero. The cone uses its original face and the supplied cylinder; restriction is not
assumed surjective on K-zero. Constructing a coefficient-natural localization null is separate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- Honest section K-zero cokernel exactness identifies the original cone descent at zero. -/
theorem boundedFlatAffineFullOpenSectionConeDesc_stable_zero_bijective (a : Under R)
    (N : Homotopy
      (prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a) ≫
        (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a)
      (zeroHom ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a)
        ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a))) :
    Function.Bijective ((stableHomotopyFunctor 0).map
      (mappingConeDesc (prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a))
        ((boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a) N)) := by
  let W := boundedFlatAffineSectionOpenModel (inclusion j a)
  let V := boundedFlatAffineFullOpenSectionModel j a
  let G := boundedFlatAffineFullOpenGradedSectionModel j a
  let fr : W ⟶ V := boundedFlatAffineSectionFullOpenModelMap j a
  let fq : V ⟶ G := boundedFlatAffineFullOpenSectionGradingModelMap j a
  let r := prespectrumMap fr
  let q := prespectrumMap fq
  let eW := levelOneStableEquiv (prespectrum W) (prespectrum_isOmega W) 0
  let eV := levelOneStableEquiv (prespectrum V) (prespectrum_isOmega V) 0
  let eG := levelOneStableEquiv (prespectrum G) (prespectrum_isOmega G) 0
  have nq (x : V.waldhausen.K 0) :
      (stableHomotopyFunctor 0).map q (eV (Additive.ofMul x)) =
        eG (Additive.ofMul (KMap fq.exact 0 x)) :=
    (prespectrumMap_KMap_stable_naturality fq 0 x).symm
  have hf : IsStableEquivalence (mappingConeFiberComparison r) :=
    prespectrum_mappingConeFiberComparison_isStableEquivalence r
  let : Subsingleton (stableHomotopyGroup (prespectrum W) (-1)) :=
    prespectrum_stableHomotopyGroup_neg_subsingleton W (-1) (by omega)
  change Function.Bijective ((stableHomotopyFunctor 0).map (mappingConeDesc r q N))
  apply mappingConeDesc_stable_zero_bijective r q N hf
  · intro x
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := eV.surjective x
      have hz : KMap fq.exact 0 z.toMul = 1 := by
        have h := eG.injective ((nq z.toMul).symm.trans (hx.trans (map_zero eG).symm))
        exact congrArg Additive.toMul h
      have he : (KMap fr.exact 0).range = (KMap fq.exact 0).ker :=
        boundedFlatAffineFullOpenSection_changeWeakKMap_zero_range_ker j a
      have hz' : z.toMul ∈ (KMap fr.exact 0).range := by
        rw [he]
        exact hz
      obtain ⟨w, hw⟩ := hz'
      exact ⟨eW (Additive.ofMul w),
        (prespectrumMap_KMap_stable_naturality fr 0 w).symm.trans
          (congrArg (fun y ↦ eV (Additive.ofMul y)) hw)⟩
    · rintro ⟨z, hz⟩
      have hc : (stableHomotopyFunctor 0).map r ≫ (stableHomotopyFunctor 0).map q = 0 :=
        ((stableHomotopyFunctor 0).map_comp r q).symm.trans
          ((N.stableHomotopyMap_eq 0).trans
            (stableHomotopyMap_zero (prespectrum W) (prespectrum G) 0))
      exact (congrArg ((stableHomotopyFunctor 0).map q) hz).symm.trans
        (ConcreteCategory.congr_hom hc z)
  · exact prespectrumMap_stable_nonnegative_surjective fq 0
      (boundedFlatAffineFullOpenSection_changeWeakKMap_zero_surjective j a)

/-- Actual section cofinality makes the original stable restriction injective in every degree. -/
theorem boundedFlatAffineFullOpenSectionRestriction_stable_injective (a : Under R) (d : ℤ) :
    Function.Injective ((stableHomotopyFunctor d).map
      (prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a))) := by
  by_cases hd : d < 0
  · intro x y _
    exact (prespectrum_stableHomotopyGroup_neg_subsingleton
      (boundedFlatAffineSectionOpenModel (inclusion j a)) d hd).elim x y
  · have he : d = (d.toNat : ℤ) := by omega
    rw [he]
    exact prespectrumMap_stable_nonnegative_injective
      (boundedFlatAffineSectionFullOpenModelMap j a) d.toNat
      (boundedFlatAffineFullOpenSectionRestriction_KMap_injective j a d.toNat)

/-- The original stable restriction is surjective away from its genuine K-zero image. -/
theorem boundedFlatAffineFullOpenSectionRestriction_stable_surjective_of_ne_zero
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Function.Surjective ((stableHomotopyFunctor d).map
      (prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a))) := by
  by_cases hn : d < 0
  · intro x
    exact ⟨0, (prespectrum_stableHomotopyGroup_neg_subsingleton
      (boundedFlatAffineFullOpenSectionModel j a) d hn).elim _ _⟩
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    have hs : Function.Surjective
        (KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) d.toNat) := by
      rw [hp]
      exact (boundedFlatAffineFullOpenSectionRestriction_KMap_succ_bijective j a
        (d.toNat - 1)).surjective
    rw [he]
    exact prespectrumMap_stable_nonnegative_surjective
      (boundedFlatAffineSectionFullOpenModelMap j a) d.toNat hs

/-- The original section restriction cone has no stable classes outside degree zero.
The degree-one kernel term uses genuine K-zero injectivity of restriction. -/
theorem boundedFlatAffineFullOpenSectionCone_stable_subsingleton
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (stableHomotopyGroup
      (mappingCone (prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a))) d) := by
  let r := prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a)
  let hr := prespectrum_mappingConeFiberComparison_isStableEquivalence r
  have hs : Function.Surjective ((stableHomotopyFunctor (d - 1 + 1)).map r) :=
    boundedFlatAffineFullOpenSectionRestriction_stable_surjective_of_ne_zero j a
      (d - 1 + 1) (by omega)
  have hi := boundedFlatAffineFullOpenSectionRestriction_stable_injective j a (d - 1)
  have hzero : ∀ x : stableHomotopyGroup (mappingCone r) (d - 1 + 1), x = 0 := by
    intro x
    have hb : stableMappingConeConnecting r hr (d - 1) x = 0 :=
      hi (((stableMappingConeConnecting_exact_source r hr (d - 1) _).mpr ⟨x, rfl⟩).trans
        (map_zero ((stableHomotopyFunctor (d - 1)).map r).hom).symm)
    obtain ⟨y, hy⟩ := (stableMappingConeConnecting_exact_cone r hr (d - 1) x).mp hb
    obtain ⟨z, rfl⟩ := hs y
    exact hy.symm.trans ((stableMappingCone_exact_target r hr (d - 1 + 1) _).mpr ⟨z, rfl⟩)
  have hz : Subsingleton (stableHomotopyGroup (mappingCone r) (d - 1 + 1)) :=
    ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
  change Subsingleton (stableHomotopyGroup (mappingCone r) d)
  exact Eq.mp (congrArg (fun k : ℤ ↦ Subsingleton (stableHomotopyGroup (mappingCone r) k))
    (sub_add_cancel d 1)) hz

/-- The actual cone descent is stable for any specified null of the original section maps.
Only open immersion and compactness of the initial open are geometric hypotheses. -/
theorem boundedFlatAffineFullOpenSectionConeDesc_isStableEquivalence (a : Under R)
    (N : Homotopy
      (prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a) ≫
        (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a)
      (zeroHom ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a)
        ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a))) :
    IsStableEquivalence
      (mappingConeDesc (prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a))
        ((boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a) N) := by
  intro d
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  by_cases hd : d = 0
  · subst d
    exact boundedFlatAffineFullOpenSectionConeDesc_stable_zero_bijective j a N
  · constructor
    · intro x y _
      exact (boundedFlatAffineFullOpenSectionCone_stable_subsingleton j a d hd).elim x y
    · intro y
      exact ⟨0, (boundedFlatAffineFullOpenGradedSection_stable_subsingleton j a d hd).elim _ _⟩

end Quillen.PerfectComplexes
