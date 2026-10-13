/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OppositeJointData
public import Quillen.AlgebraicGeometry.PerfectComplexes.StrictOpenRelative

/-! # Original relative-open strict-to-perfect comparison and dual restriction -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
open Waldhausen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Original perfect restriction preserves the actual opposite structures. -/
theorem perfectRestrict_op_exact : IsExact
    (perfectOppositeWaldhausen X).cof (perfectOppositeWaldhausen X).weq
    (perfectOppositeWaldhausen U).cof (perfectOppositeWaldhausen U).weq
    (perfectRestrict j).op where
  zero hZ := (perfectRestrict j).op.map_isZero hZ
  cofibration f hf := (perfectExactRestrict j).map_deflation f.unop hf
  weak f hf := (perfectRestrict_waldhausenExact j).weak f.unop hf
  pushout hi hs := ((perfectExactRestrict j).map_isPullback hs.unop hi).op

/-- Original strict restriction preserves the actual opposite structures. -/
theorem strictRestrict_op_exact : IsExact
    (strictOppositeWaldhausen X).cof (strictOppositeWaldhausen X).weq
    (strictOppositeWaldhausen U).cof (strictOppositeWaldhausen U).weq
    (strictRestrict j).op where
  zero hZ := (strictRestrict j).op.map_isZero hZ
  cofibration f hf := (strictExactRestrict j).map_deflation f.unop hf
  weak f hf := (strictRestrict_waldhausenExact j).weak f.unop hf
  pushout hi hs := ((strictExactRestrict j).map_isPullback hs.unop hi).op

/-- The unchanged strict-to-perfect inclusion is exact for relative quasi-isomorphisms. -/
theorem strictToPerfectOpen_waldhausenExact : IsExact
    (StrictOpenWeakImage.coarseWaldhausen j).cof (StrictOpenWeakImage.coarseWaldhausen j).weq
    (perfectOpenWeakWaldhausen j).cof (perfectOpenWeakWaldhausen j).weq (strictToPerfect X) where
  zero := (subcategoryInclusion_exact (strictPerfect X) (locallyPerfect X)
    (fun _ h => locallyPerfect_of_strictPerfect h)).zero
  cofibration := (subcategoryInclusion_exact (strictPerfect X) (locallyPerfect X)
    (fun _ h => locallyPerfect_of_strictPerfect h)).cofibration
  weak _ h := h
  pushout := (subcategoryInclusion_exact (strictPerfect X) (locallyPerfect X)
    (fun _ h => locallyPerfect_of_strictPerfect h)).pushout

/-- Actual relative-open comparison on the original canonical K-groups. -/
def strictToPerfectOpenKMap (n : ℕ) :
    (StrictOpenWeakImage.coarseWaldhausen j).K n →* PerfectOpenK j n :=
  KMap (strictToPerfectOpen_waldhausenExact j) n

end Quillen.PerfectComplexes
