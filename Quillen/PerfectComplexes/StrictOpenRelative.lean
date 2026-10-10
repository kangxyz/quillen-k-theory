/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.Restriction
import Quillen.Waldhausen.Functoriality.KMap
import Quillen.PerfectComplexes.Closure
import Quillen.Waldhausen.Fibration.InverseImageWeak
import Quillen.Waldhausen.Fibration.Rows.CoarseJoint
import Quillen.Waldhausen.Fibration.Rows.ComplexRelativeJoint

/-! # The genuine original relative-open strict-perfect Waldhausen model

Only the weak class is changed to quasi-isomorphisms after original open
restriction. The original strict cone cylinder gives actual functorial
factorization and coarse joint data. The canonical relative K-map factors
the existing original strict restriction K-map. No approximation or
cofinality property for an arbitrary open is asserted.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.StrictOpenWeakImage
open Waldhausen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual strict complexes with relative quasi-isomorphisms detected on the open. -/
def coarseWaldhausen : Structure (StrictPerfect X) :=
  Structure.withInverseImageWeak (strictRestrict_waldhausenExact j)

/-- The original strict weak class is contained in the genuine relative class. -/
def nested : Fibration.NestedWeakEquivalences (strictWaldhausen X) :=
  Structure.inverseImageWeakNested (strictRestrict_waldhausenExact j)

/-- The original strict restriction is genuinely exact for the relative structure. -/
theorem restriction_exact : IsExact (coarseWaldhausen j).cof (coarseWaldhausen j).weq
    (strictWaldhausen U).cof (strictWaldhausen U).weq (strictRestrict j) :=
  Structure.withInverseImageWeak_exact (strictRestrict_waldhausenExact j)

/-- Relative saturation comes from actual restricted quasi-isomorphisms. -/
instance coarse_twoOutOfThree : (coarseWaldhausen j).weq.HasTwoOutOfThreeProperty := by
  let : (strictWaldhausen U).weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs (subcategoryWeakEquivalences (strictPerfect U)).HasTwoOutOfThreeProperty
  exact Structure.withInverseImageWeak_twoOutOfThree (strictRestrict_waldhausenExact j)

/-- The genuine original cone factorization is retained in the strict relative model. -/
def sourceFactorization : FunctorialFactorization (coarseWaldhausen j) := by
  let T := Fibration.complexSubcategoryFactorization (strictPerfect X)
    (fun hK hL f ↦ strictPerfect_mappingCone hK hL f)
  exact { T with weak := fun f ↦ (nested j).le_weq _ (T.weak f) }

/-- Actual fine joint data comes from the original strict complex cone and shift. -/
def jointData : Fibration.RowFactorization.JointData (nested j) :=
  Fibration.complexJointDataOfNested (strictPerfect X)
    (fun hK hL f ↦ strictPerfect_mappingCone hK hL f)
    (fun _ hK ↦ strictPerfect_shift hK 1) (nested j)

/-- The original joint cylinder is genuinely exact for the coarse class. -/
def coarseJointData : Fibration.RowFactorization.JointData
    (Fibration.NestedWeakEquivalences.refl (coarseWaldhausen j)) := by
  let : (nested j).coarse.weq.HasTwoOutOfThreeProperty := coarse_twoOutOfThree j
  exact (jointData j).coarseReflexive (nested j)

/-- Original relative restriction on the actual canonical connective K-groups. -/
def relativeKRestrict (n : ℕ) : (coarseWaldhausen j).K n →* StrictK U n :=
  KMap (restriction_exact j) n

/-- The relative factorization retains the entire original strict restriction K-map. -/
theorem relativeKRestrict_comp_changeWeak (n : ℕ) :
    (relativeKRestrict j n).comp (KMap (Fibration.changeWeak_exact (nested j)) n) = strictKRestrict j n := by
  unfold relativeKRestrict strictKRestrict
  rw [← KMap_comp]

end Quillen.PerfectComplexes.StrictOpenWeakImage
