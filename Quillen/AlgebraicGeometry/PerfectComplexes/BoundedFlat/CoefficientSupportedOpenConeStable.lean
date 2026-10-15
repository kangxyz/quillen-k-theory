/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenKZeroExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenNull
public import Quillen.Waldhausen.SConstruction.Iterated.StableKMap
public import Quillen.Waldhausen.SConstruction.Iterated.ConeFiberExcision
public import Quillen.Topology.Prespectrum.ConeDescCofinality

/-!
# The actual supported native restriction cone and its original image grading

Supported joint-cylinder data prove positive graded K-vanishing. Original
Model connectivity gives negative stable vanishing, and the actual K-to-stable
dictionary transports supported r_Z cofinality. Honest supported K-zero image
exactness and q_Z surjectivity identify the initial cone descent at degree zero.

The signed cone theorem applies to every genuinely typed null. Its canonical
specialization retains the same coefficient-natural reversed zero-to-image
null, actual inclusion face and every original cylinder time. Stability uses
compact P, Q and auxiliary support complement T, and quasi-separated Q; the
construction and its naturality use only compact P and Q. No seed, telescope
or classical comparison is asserted.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original positive graded K-groups identify with the same Model's positive stable groups. -/
theorem boundedFlatCoefficientSupportedGradedOpen_stable_succ_subsingleton (a : Under R) (n : ℕ) :
    Subsingleton (stableHomotopyGroup (prespectrum
      (boundedFlatCoefficientSupportedGradedOpenModel f T a))
      ((n + 1 : ℕ) : ℤ)) := by
  let : Subsingleton
      ((boundedFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.K (n + 1)) :=
    boundedFlatCoefficientSupportedGradedOpen_K_succ_subsingleton f T a n
  let e : Additive
      ((boundedFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.K (n + 1)) ≃+
      stableHomotopyGroup (prespectrum (boundedFlatCoefficientSupportedGradedOpenModel f T a))
        ((n + 1 : ℕ) : ℤ) :=
    levelOneStableEquiv (prespectrum (boundedFlatCoefficientSupportedGradedOpenModel f T a))
      (prespectrum_isOmega (boundedFlatCoefficientSupportedGradedOpenModel f T a)) (n + 1)
  exact e.symm.injective.subsingleton

/-- Actual Model connectivity gives negative signed stable vanishing without compactness. -/
theorem boundedFlatCoefficientSupportedGradedOpen_stable_neg_subsingleton
    (a : Under R) (d : ℤ) (hd : d < 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedFlatCoefficientSupportedGradedOpenModel f T a)) d) :=
  prespectrum_stableHomotopyGroup_neg_subsingleton
    (boundedFlatCoefficientSupportedGradedOpenModel f T a) d hd

/-- The actual pointwise graded Model has no signed stable classes outside degree zero. -/
theorem boundedFlatCoefficientSupportedGradedOpen_stable_subsingleton
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedFlatCoefficientSupportedGradedOpenModel f T a)) d) := by
  by_cases hn : d < 0
  · exact boundedFlatCoefficientSupportedGradedOpen_stable_neg_subsingleton f T a d hn
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    rw [he, hp]
    exact boundedFlatCoefficientSupportedGradedOpen_stable_succ_subsingleton f T a (d.toNat - 1)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Honest original K-zero exactness identifies every specified native cone descent at zero. -/
theorem boundedFlatCoefficientSupportedOpenConeDesc_stable_zero_bijective (a : Under R)
    (N : Homotopy
      ((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a ≫
        (boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a)
      (zeroHom ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)
        ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a))) :
    Function.Bijective ((stableHomotopyFunctor 0).map
      (mappingConeDesc ((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation
        f T).app a)
        ((boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a) N)) := by
  let W := boundedFlatCoefficientSupportedOpenModel f T a
  let V := (boundedFlatCoefficientSupportedFullOpenModelFunctor f T).obj a
  let G := boundedFlatCoefficientSupportedGradedOpenModel f T a
  let fr : W ⟶ V := boundedFlatCoefficientSupportedOpenRestrictionModelMap f T a
  let fq : V ⟶ G := boundedFlatCoefficientSupportedOpenGradingModelMap f T a
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
        boundedFlatCoefficientSupportedOpenGrading_KMap_zero_range_ker f T a
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
      (boundedFlatCoefficientSupportedOpenGrading_KMap_zero_surjective f T a)

variable [QuasiSeparatedSpace Q.left] [CompactSpace T]

/-- Original r cofinality and Model connectivity prove injectivity in every signed degree. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_stable_injective (a : Under R) (d : ℤ) :
    Function.Injective ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a)) := by
  by_cases hd : d < 0
  · intro x y _
    exact (prespectrum_stableHomotopyGroup_neg_subsingleton
      (boundedFlatCoefficientSupportedOpenModel f T a) d hd).elim x y
  · have he : d = (d.toNat : ℤ) := by omega
    rw [he]
    exact prespectrumMap_stable_nonnegative_injective
      (boundedFlatCoefficientSupportedOpenRestrictionModelMap f T a) d.toNat
      (boundedFlatCoefficientSupportedOpenRestriction_KMap_injective f T a d.toNat)

/-- The same original signed r map is surjective away from its honest degree-zero image. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_stable_surjective_of_ne_zero
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Function.Surjective ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a)) := by
  by_cases hn : d < 0
  · intro x
    exact ⟨0, (prespectrum_stableHomotopyGroup_neg_subsingleton
      ((boundedFlatCoefficientSupportedFullOpenModelFunctor f T).obj a) d hn).elim _ _⟩
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    have hs : Function.Surjective
        (KMap (boundedFlatCoefficientSupportedOpenRestriction_exact f T a) d.toNat) := by
      rw [hp]
      exact (boundedFlatCoefficientSupportedOpenRestriction_KMap_succ_bijective f T a
        (d.toNat - 1)).surjective
    rw [he]
    exact prespectrumMap_stable_nonnegative_surjective
      (boundedFlatCoefficientSupportedOpenRestrictionModelMap f T a) d.toNat hs

/-- Genuine Model excision and original r/q facts prove every specified descent stable. -/
theorem boundedFlatCoefficientSupportedOpenConeDesc_isStableEquivalence (a : Under R)
    (N : Homotopy
      ((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a ≫
        (boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a)
      (zeroHom ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)
        ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a))) :
    IsStableEquivalence
      (mappingConeDesc ((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation
        f T).app a)
        ((boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a) N) := by
  apply mappingConeDesc_isStableEquivalence_of_cofinality
  · exact prespectrum_mappingConeFiberComparison_isStableEquivalence
      (prespectrumMap (boundedFlatCoefficientSupportedOpenRestrictionModelMap f T a))
  · exact boundedFlatCoefficientSupportedOpenRestriction_stable_injective f T a
  · exact boundedFlatCoefficientSupportedOpenRestriction_stable_surjective_of_ne_zero f T a
  · exact boundedFlatCoefficientSupportedGradedOpen_stable_subsingleton f T a
  · exact boundedFlatCoefficientSupportedOpenConeDesc_stable_zero_bijective f T a N

omit [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- The actual initial cone comparison specializes to the unchanged canonical whole null. -/
def boundedFlatCoefficientSupportedOpenGradingConeComparison (a : Under R) :
    mappingCone
      ((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a) ⟶
      (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a :=
  mappingConeDesc
    ((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a)
    ((boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a)
    ((boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a)

omit [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- The original cone inclusion face is exactly the actual q component. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedOpenGradingConeComparison_inclusion (a : Under R) :
    mappingConeInclusion
        ((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a) ≫
        boundedFlatCoefficientSupportedOpenGradingConeComparison f T a =
      (boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a :=
  mappingConeInclusion_desc _ _ _

omit [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- Every original cone cylinder point retains the same canonical whole-null time. -/
theorem boundedFlatCoefficientSupportedOpenGradingConeComparison_cylinder (a : Under R)
    (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    (boundedFlatCoefficientSupportedOpenGradingConeComparison f T a).map n
      (ReducedMappingCone.cylinder
        (((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).point n)
        (((boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T).obj a).point n)
        (((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation
          f T).app a).map n)
        (s, x)) =
      ((boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a).level n (s, x) := rfl

/-- The canonical whole-null specialization is stable in all integer degrees. -/
theorem boundedFlatCoefficientSupportedOpenGradingConeComparison_isStableEquivalence (a : Under R) :
    IsStableEquivalence (boundedFlatCoefficientSupportedOpenGradingConeComparison f T a) :=
  boundedFlatCoefficientSupportedOpenConeDesc_isStableEquivalence f T a
    ((boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a)

omit [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- The unchanged whole null supplies the actual coefficient-natural cone comparison. -/
def boundedFlatCoefficientSupportedOpenGradingConeComparisonTransformation :
    mappingConeDiagram
      (boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T) ⟶
      boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T :=
  mappingConeDescTransformation
    (boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (fun a ↦ (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a)
    (fun {_ _} g ↦ (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).naturality g)

omit [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- Each coefficient component retains precisely the original canonical cone descent. -/
theorem boundedFlatCoefficientSupportedOpenGradingConeComparisonTransformation_app (a : Under R) :
    (boundedFlatCoefficientSupportedOpenGradingConeComparisonTransformation f T).app a =
      boundedFlatCoefficientSupportedOpenGradingConeComparison f T a := rfl

end Quillen.PerfectComplexes
