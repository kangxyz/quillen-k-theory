/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDeficitCokernel

/-!
# Original coarse-to-full-open deficit consumers

The exact original restriction, cone face and image quotient are retained. Compact-open qcqs
cofinality is used for concentration, while the actual zero-degree cokernel needs no density.
No Bass transition or telescope vanishing is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.OpenDeficit
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The unchanged original absolute restriction classes vanish through the actual cone face. -/
theorem originalRestrictedClass (a : PerfectK X 0) :
    (stableHomotopyFunctor 0).map (mappingConeInclusion (perfectOpenRestrictPrespectrumMap j))
        (originalKStableEquiv (perfectWaldhausen U) 0
          (Additive.ofMul (perfectKRestrict j 0 a))) = 0 :=
  (perfectOpenDeficitZeroProjection_exact j _).mpr ⟨Additive.ofMul a, rfl⟩

/-- An original open class has zero deficit exactly when it lies in the original ambient image. -/
theorem originalImageCriterion (a : PerfectK U 0) :
    perfectOpenDeficitZeroProjection j (Additive.ofMul a) = 0 ↔
      a ∈ (perfectKRestrict j 0).range := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (perfectOpenDeficitZeroProjection_exact j _).mp h
    exact ⟨b.toMul, congrArg Additive.toMul hb⟩
  · rintro ⟨b, rfl⟩
    exact (perfectOpenDeficitZeroProjection_exact j _).mpr ⟨Additive.ofMul b, rfl⟩

/-- The canonical quotient isomorphism retains each original open class before its cone inclusion.
-/
theorem originalQuotientRepresentative (a : PerfectK U 0) :
    (perfectOpenDeficitZeroQuotientIso j).hom (QuotientAddGroup.mk (Additive.ofMul a)) =
      perfectOpenDeficitZeroProjection j (Additive.ofMul a) :=
  perfectOpenDeficitZeroQuotientIso_mk j a

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]

/-- Every genuine negative class of this original connective deficit is zero. -/
theorem originalNegativeClass (q : ℕ)
    (x : stableHomotopyGroup (perfectOpenDeficit j) (-((q : ℤ) + 1))) : x = 0 := by
  let := perfectOpenDeficit_stableHomotopyGroup_subsingleton j (-((q : ℤ) + 1)) (by omega)
  exact Subsingleton.elim _ _

/-- The original signed degree-one boundary is zero using the genuine K-zero injectivity. -/
theorem originalDegreeOneBoundary
    (x : stableHomotopyGroup (perfectOpenDeficit j) 1) :
    stableMappingConeConnecting (perfectOpenRestrictPrespectrumMap j)
      (perfectOpenRestrictPrespectrumMap_coneFiber_isStableEquivalence j) 0 x = 0 := by
  let := perfectOpenDeficit_stableHomotopyGroup_subsingleton j 1 (by omega)
  rw [Subsingleton.elim x 0]
  exact map_zero (stableMappingConeConnecting (perfectOpenRestrictPrespectrumMap j)
    (perfectOpenRestrictPrespectrumMap_coneFiber_isStableEquivalence j) 0).hom

end Quillen.Tests.OpenDeficit
