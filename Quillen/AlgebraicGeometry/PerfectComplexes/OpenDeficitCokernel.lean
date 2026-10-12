/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDeficit
public import Quillen.Topology.Prespectrum.ConeStableCokernel
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Mathlib.Algebra.Category.Grp.Colimits

/-!
# The actual K-zero restriction cokernel of the original open deficit

The original cone inclusion, after the original stable K comparison, is the cokernel of the
unchanged absolute restriction on K-zero. Its canonical isomorphism retains every original
open K-zero representative. This cokernel description itself holds for any open immersion;
qcqs and quasi-compact-open hypotheses enter the separate concentration theorem.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Only the proved commutativity is added; the original K-zero operations are unchanged. -/
local instance perfectDeficitKZeroCommGroup (S : Scheme.{u}) : CommGroup (PerfectK S 0) :=
  Quillen.Waldhausen.Additivity.KCommGroup (perfectWaldhausen S) 0

/-- The original absolute K-zero restriction, with only its group law written additively. -/
def perfectKRestrictZeroHom :
    AddCommGrpCat.of (Additive (PerfectK X 0)) ⟶ AddCommGrpCat.of (Additive (PerfectK U 0)) :=
  AddCommGrpCat.ofHom (perfectKRestrict j 0).toAdditive

/-- The literal original cone face after the original comparison from open K-zero. -/
def perfectOpenDeficitZeroProjection :
    AddCommGrpCat.of (Additive (PerfectK U 0)) ⟶
      stableHomotopyGroup (perfectOpenDeficit j) 0 :=
  (originalKStableEquiv (perfectWaldhausen U) 0).toAddCommGrpIso.hom ≫
    (stableHomotopyFunctor 0).map (mappingConeInclusion (perfectOpenRestrictPrespectrumMap j))

/-- Every actual zero-degree deficit class has an original open K-zero representative. -/
theorem perfectOpenDeficitZeroProjection_surjective :
    Function.Surjective (perfectOpenDeficitZeroProjection j) := by
  let := originalStableHomotopyGroup_neg_subsingleton (perfectOpenWeakWaldhausen j) (-1) (by omega)
  intro x
  obtain ⟨y, hy⟩ := stableMappingConeInclusion_zero_surjective
    (perfectOpenRestrictPrespectrumMap j)
    (perfectOpenRestrictPrespectrumMap_coneFiber_isStableEquivalence j) x
  obtain ⟨a, rfl⟩ := (originalKStableEquiv (perfectWaldhausen U) 0).surjective y
  exact ⟨a, hy⟩

/-- The exact original kernel is the image of absolute restriction, without a density premise. -/
theorem perfectOpenDeficitZeroProjection_exact :
    Function.Exact (perfectKRestrictZeroHom j) (perfectOpenDeficitZeroProjection j) := by
  let f := perfectOpenRestrictPrespectrumMap j
  let hf := perfectOpenRestrictPrespectrumMap_coneFiber_isStableEquivalence j
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (stableMappingCone_exact_target f hf 0
      (originalKStableEquiv (perfectWaldhausen U) 0 x)).mp hx
    obtain ⟨a, rfl⟩ := (originalKStableEquiv (perfectOpenWeakWaldhausen j) 0).surjective y
    have ha := (originalKStableEquiv (perfectWaldhausen U) 0).injective
      ((perfectOpenRestrictPrespectrumMap_stable_naturality j 0 a.toMul).symm.trans hy)
    obtain ⟨b, hb⟩ := perfectOpenKMap_zero_surjective j a.toMul
    refine ⟨Additive.ofMul b, ?_⟩
    change Additive.ofMul (perfectKRestrict j 0 b) = x
    have h := (DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap j 0) b).symm.trans
      (congrArg (perfectOpenKRestrict j 0) hb)
    exact (congrArg Additive.ofMul h).trans ha
  · rintro ⟨b, rfl⟩
    apply (stableMappingCone_exact_target f hf 0 _).mpr
    refine ⟨originalKStableEquiv (perfectOpenWeakWaldhausen j) 0
      (Additive.ofMul (perfectOpenKMap j 0 b.toMul)), ?_⟩
    exact (perfectOpenRestrictPrespectrumMap_stable_naturality j 0
      (perfectOpenKMap j 0 b.toMul)).trans
      (congrArg (fun a ↦ originalKStableEquiv (perfectWaldhausen U) 0 (Additive.ofMul a))
        (DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap j 0) b.toMul))

/-- The two original arrows define the actual degree-zero deficit short complex. -/
def perfectOpenDeficitZeroShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (perfectKRestrictZeroHom j) (perfectOpenDeficitZeroProjection j) (by
    ext x
    exact (perfectOpenDeficitZeroProjection_exact j _).mpr ⟨x, rfl⟩)

/-- Original excision and the exact restriction image give the genuine cokernel property. -/
def perfectOpenDeficitZeroIsCokernel :
    IsColimit (CokernelCofork.ofπ (perfectOpenDeficitZeroProjection j)
      (perfectOpenDeficitZeroShortComplex j).zero) := by
  have : Epi ((perfectOpenDeficitZeroShortComplex j).g) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (perfectOpenDeficitZeroProjection_surjective j)
  have he : (perfectOpenDeficitZeroShortComplex j).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    exact (perfectOpenDeficitZeroProjection_exact j x).mp hx
  exact he.gIsCokernel

/-- The exact original absolute restriction cokernel computes the actual deficit group. -/
def perfectOpenDeficitZeroCokernelIso :
    cokernel (perfectKRestrictZeroHom j) ≅ stableHomotopyGroup (perfectOpenDeficit j) 0 :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (perfectOpenDeficitZeroIsCokernel j)

/-- Every original open K-zero class maps through the same original cone face. -/
@[reassoc]
theorem perfectOpenDeficitZeroCokernelIso_π :
    cokernel.π (perfectKRestrictZeroHom j) ≫ (perfectOpenDeficitZeroCokernelIso j).hom =
      perfectOpenDeficitZeroProjection j :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom
    (perfectOpenDeficitZeroIsCokernel j) WalkingParallelPair.one

/-- The actual deficit group is precisely the quotient by the original restriction image. -/
def perfectOpenDeficitZeroQuotientIso :
    AddCommGrpCat.of (Additive (PerfectK U 0) ⧸ (perfectKRestrictZeroHom j).hom.range) ≅
      stableHomotopyGroup (perfectOpenDeficit j) 0 :=
  (AddCommGrpCat.cokernelIsoQuotient (perfectKRestrictZeroHom j)).symm ≪≫
    perfectOpenDeficitZeroCokernelIso j

/-- The quotient comparison preserves each original representative and its literal cone image. -/
theorem perfectOpenDeficitZeroQuotientIso_mk (a : PerfectK U 0) :
    (perfectOpenDeficitZeroQuotientIso j).hom (QuotientAddGroup.mk (Additive.ofMul a)) =
      (stableHomotopyFunctor 0).map (mappingConeInclusion (perfectOpenRestrictPrespectrumMap j))
        (originalKStableEquiv (perfectWaldhausen U) 0 (Additive.ofMul a)) := by
  change (perfectOpenDeficitZeroCokernelIso j).hom
    (cokernel.π (perfectKRestrictZeroHom j) (Additive.ofMul a)) = _
  exact ConcreteCategory.congr_hom (perfectOpenDeficitZeroCokernelIso_π j) (Additive.ofMul a)

end Quillen.PerfectComplexes
