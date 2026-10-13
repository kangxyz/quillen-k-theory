/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.KTheory
public import Quillen.Waldhausen.GrothendieckComparison.SmallModel

/-! # The original Waldhausen presentation of literal perfect-complex K₀

The original locally perfect complex model has distinct object and morphism
universes. The genuine universe bridge identifies its original weak-arrow and
cofibration-pushout Grothendieck presentation with its literal existing PerfectK.
This does not identify that presentation with a triangulated derived-category
presentation; that requires a separate triangle/cofibration comparison.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen.AlgebraicGrothendieck

/-- The original locally perfect Waldhausen presentation computes the unchanged PerfectK₀. -/
def perfectGrothendieckKZeroEquiv (X : Scheme.{u}) :
    Multiplicative (Group (perfectWaldhausen X)) ≃* PerfectK X 0 :=
  grothendieckKZeroEquivOfSmallModel (perfectWaldhausen X)

/-- The literal original perfect-complex object class maps to its original topological loop. -/
@[simp] theorem perfectGrothendieckKZeroEquiv_objectClass (X : Scheme.{u}) (A : Perfect X) :
    perfectGrothendieckKZeroEquiv X
      (Multiplicative.ofAdd (objectClass (perfectWaldhausen X) A)) =
        (perfectWaldhausen X).kZeroObjectClass A :=
  grothendieckKZeroEquivOfSmallModel_objectClass (perfectWaldhausen X) A

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Original open restriction respects every original classical perfect-complex class. -/
theorem perfectGrothendieckKZeroEquiv_restrict
    (a : Multiplicative (Group (perfectWaldhausen X))) :
    perfectKRestrict j 0 (perfectGrothendieckKZeroEquiv X a) =
      perfectGrothendieckKZeroEquiv U
        ((map (perfectWaldhausen X) (perfectRestrict j)
          (perfectRestrict_waldhausenExact j)).toMultiplicative a) :=
  grothendieckKZeroEquivOfSmallModel_natural (perfectWaldhausen X) (perfectWaldhausen U)
    (perfectRestrict j) (perfectRestrict_waldhausenExact j) a

/-- The original open restriction is detected by the classical inverse on all literal PerfectK₀. -/
theorem perfectGrothendieckKZeroEquiv_symm_restrict (x : PerfectK X 0) :
    (perfectGrothendieckKZeroEquiv U).symm (perfectKRestrict j 0 x) =
      (map (perfectWaldhausen X) (perfectRestrict j)
        (perfectRestrict_waldhausenExact j)).toMultiplicative
          ((perfectGrothendieckKZeroEquiv X).symm x) :=
  grothendieckKZeroEquivOfSmallModel_symm_natural (perfectWaldhausen X) (perfectWaldhausen U)
    (perfectRestrict j) (perfectRestrict_waldhausenExact j) x

end Quillen.PerfectComplexes
