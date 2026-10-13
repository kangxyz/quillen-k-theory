/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenKZeroExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenNull
public import Quillen.Waldhausen.SConstruction.Iterated.StableKMap
public import Quillen.Waldhausen.SConstruction.Iterated.ConeFiberExcision
public import Quillen.Topology.Prespectrum.ConeDescCofinality

/-!
# The actual global native restriction cone and original quotient grading

The original positive graded K-groups and actual Model connectivity give signed
stable concentration of G. The same K-to-stable dictionary transports original
r cofinality. Honest K-zero image/kernel exactness and q-zero surjectivity then
identify the original cone descent in degree zero.

The generic signed cone theorem proves every specified genuinely typed null
gives a stable descent. Its canonical specialization uses precisely the whole
coefficient-natural reversed zero-to-image null already constructed on this
C/F/G family. The original inclusion face and every cylinder time are retained.
No Laurent seed, completion or classical K-theory comparison is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Original positive graded K-groups identify with the same Model's positive stable groups. -/
theorem boundedFlatCoefficientGradedOpen_stable_succ_subsingleton (a : Under R) (n : ℕ) :
    Subsingleton (stableHomotopyGroup (prespectrum (boundedFlatCoefficientGradedOpenModel f a))
      ((n + 1 : ℕ) : ℤ)) := by
  let : Subsingleton ((boundedFlatCoefficientFullOpenGrading f a).coarseStructure.K (n + 1)) :=
    boundedFlatCoefficientGradedOpen_K_succ_subsingleton f a n
  let e : Additive ((boundedFlatCoefficientFullOpenGrading f a).coarseStructure.K (n + 1)) ≃+
      stableHomotopyGroup (prespectrum (boundedFlatCoefficientGradedOpenModel f a))
        ((n + 1 : ℕ) : ℤ) :=
    levelOneStableEquiv (prespectrum (boundedFlatCoefficientGradedOpenModel f a))
      (prespectrum_isOmega (boundedFlatCoefficientGradedOpenModel f a)) (n + 1)
  exact e.symm.injective.subsingleton

/-- Actual Model connectivity gives negative signed stable vanishing without compactness. -/
theorem boundedFlatCoefficientGradedOpen_stable_neg_subsingleton
    (a : Under R) (d : ℤ) (hd : d < 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedFlatCoefficientGradedOpenModel f a)) d) :=
  prespectrum_stableHomotopyGroup_neg_subsingleton (boundedFlatCoefficientGradedOpenModel f a) d hd

/-- The actual pointwise graded Model has no signed stable classes outside degree zero. -/
theorem boundedFlatCoefficientGradedOpen_stable_subsingleton
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedFlatCoefficientGradedOpenModel f a)) d) := by
  by_cases hn : d < 0
  · exact boundedFlatCoefficientGradedOpen_stable_neg_subsingleton f a d hn
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    rw [he, hp]
    exact boundedFlatCoefficientGradedOpen_stable_succ_subsingleton f a (d.toNat - 1)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Honest original K-zero exactness identifies every specified native cone descent at zero. -/
theorem boundedFlatCoefficientOpenConeDesc_stable_zero_bijective (a : Under R)
    (N : Homotopy
      ((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a ≫
        (boundedFlatCoefficientOpenGradingPrespectrumTransformation f).app a)
      (zeroHom ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a)
        ((boundedFlatCoefficientGradedOpenPrespectrumFunctor f).obj a))) :
    Function.Bijective ((stableHomotopyFunctor 0).map
      (mappingConeDesc ((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a)
        ((boundedFlatCoefficientOpenGradingPrespectrumTransformation f).app a) N)) := by
  let W := boundedFlatCoefficientOpenModel f a
  let V := (boundedFlatCoefficientFullOpenModelFunctor f).obj a
  let G := boundedFlatCoefficientGradedOpenModel f a
  let fr : W ⟶ V := boundedFlatCoefficientOpenRestrictionModelMap f a
  let fq : V ⟶ G := boundedFlatCoefficientOpenGradingModelMap f a
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
        boundedFlatCoefficientOpenGrading_KMap_zero_range_ker f a
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
      (boundedFlatCoefficientOpenGrading_KMap_zero_surjective f a)

variable [QuasiSeparatedSpace Q.left]

/-- Original r cofinality and Model connectivity prove injectivity in every signed degree. -/
theorem boundedFlatCoefficientOpenRestriction_stable_injective (a : Under R) (d : ℤ) :
    Function.Injective ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a)) := by
  by_cases hd : d < 0
  · intro x y _
    exact (prespectrum_stableHomotopyGroup_neg_subsingleton
      (boundedFlatCoefficientOpenModel f a) d hd).elim x y
  · have he : d = (d.toNat : ℤ) := by omega
    rw [he]
    exact prespectrumMap_stable_nonnegative_injective
      (boundedFlatCoefficientOpenRestrictionModelMap f a) d.toNat
      (boundedFlatCoefficientOpenRestriction_KMap_injective f a d.toNat)

/-- The same original signed r map is surjective away from its honest degree-zero image. -/
theorem boundedFlatCoefficientOpenRestriction_stable_surjective_of_ne_zero
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Function.Surjective ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a)) := by
  by_cases hn : d < 0
  · intro x
    exact ⟨0, (prespectrum_stableHomotopyGroup_neg_subsingleton
      ((boundedFlatCoefficientFullOpenModelFunctor f).obj a) d hn).elim _ _⟩
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    have hs : Function.Surjective
        (KMap (boundedFlatCoefficientOpenRestriction_exact f a) d.toNat) := by
      rw [hp]
      exact (boundedFlatCoefficientOpenRestriction_KMap_succ_bijective f a
        (d.toNat - 1)).surjective
    rw [he]
    exact prespectrumMap_stable_nonnegative_surjective
      (boundedFlatCoefficientOpenRestrictionModelMap f a) d.toNat hs

/-- Genuine Model excision and original r/q facts prove every specified descent stable. -/
theorem boundedFlatCoefficientOpenConeDesc_isStableEquivalence (a : Under R)
    (N : Homotopy
      ((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a ≫
        (boundedFlatCoefficientOpenGradingPrespectrumTransformation f).app a)
      (zeroHom ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a)
        ((boundedFlatCoefficientGradedOpenPrespectrumFunctor f).obj a))) :
    IsStableEquivalence
      (mappingConeDesc ((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a)
        ((boundedFlatCoefficientOpenGradingPrespectrumTransformation f).app a) N) := by
  apply mappingConeDesc_isStableEquivalence_of_cofinality
  · exact prespectrum_mappingConeFiberComparison_isStableEquivalence
      (prespectrumMap (boundedFlatCoefficientOpenRestrictionModelMap f a))
  · exact boundedFlatCoefficientOpenRestriction_stable_injective f a
  · exact boundedFlatCoefficientOpenRestriction_stable_surjective_of_ne_zero f a
  · exact boundedFlatCoefficientGradedOpen_stable_subsingleton f a
  · exact boundedFlatCoefficientOpenConeDesc_stable_zero_bijective f a N

omit [QuasiSeparatedSpace Q.left] in
/-- The actual initial cone comparison specializes to the unchanged canonical whole null. -/
def boundedFlatCoefficientOpenConeComparison (a : Under R) :
    mappingCone ((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a) ⟶
      (boundedFlatCoefficientGradedOpenPrespectrumFunctor f).obj a :=
  mappingConeDesc ((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a)
    ((boundedFlatCoefficientOpenGradingPrespectrumTransformation f).app a)
    ((boundedFlatCoefficientOpenGradingDiagramNull f).homotopy a)

omit [QuasiSeparatedSpace Q.left] in
/-- The original cone inclusion face is exactly the actual q component. -/
@[reassoc] theorem boundedFlatCoefficientOpenConeComparison_inclusion (a : Under R) :
    mappingConeInclusion
        ((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a) ≫
        boundedFlatCoefficientOpenConeComparison f a =
      (boundedFlatCoefficientOpenGradingPrespectrumTransformation f).app a :=
  mappingConeInclusion_desc _ _ _

omit [QuasiSeparatedSpace Q.left] in
/-- Every original cone cylinder point retains the same canonical whole-null time. -/
theorem boundedFlatCoefficientOpenConeComparison_cylinder (a : Under R)
    (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    (boundedFlatCoefficientOpenConeComparison f a).map n
      (ReducedMappingCone.cylinder
        (((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a).point n)
        (((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj a).point n)
        (((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a).map n)
        (s, x)) =
      ((boundedFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x) := rfl

/-- The canonical whole-null specialization is stable in all integer degrees. -/
theorem boundedFlatCoefficientOpenConeComparison_isStableEquivalence (a : Under R) :
    IsStableEquivalence (boundedFlatCoefficientOpenConeComparison f a) :=
  boundedFlatCoefficientOpenConeDesc_isStableEquivalence f a
    ((boundedFlatCoefficientOpenGradingDiagramNull f).homotopy a)

omit [QuasiSeparatedSpace Q.left] in
/-- The unchanged whole null supplies the actual coefficient-natural cone comparison. -/
def boundedFlatCoefficientOpenConeComparisonTransformation :
    mappingConeDiagram (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f) ⟶
      boundedFlatCoefficientGradedOpenPrespectrumFunctor f :=
  mappingConeDescTransformation (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f)
    (boundedFlatCoefficientOpenGradingPrespectrumTransformation f)
    (fun a ↦ (boundedFlatCoefficientOpenGradingDiagramNull f).homotopy a)
    (fun {_ _} g ↦ (boundedFlatCoefficientOpenGradingDiagramNull f).naturality g)

omit [QuasiSeparatedSpace Q.left] in
/-- Each coefficient component retains precisely the original canonical cone descent. -/
theorem boundedFlatCoefficientOpenConeComparisonTransformation_app (a : Under R) :
    (boundedFlatCoefficientOpenConeComparisonTransformation f).app a =
      boundedFlatCoefficientOpenConeComparison f a := rfl

end Quillen.PerfectComplexes
