/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Restriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.VectorBundleInclusion

/-! # Open restriction on strict-perfect Waldhausen K-theory

The native strict-perfect restriction functor and inherited exact functor come
from Aglib. Their Waldhausen exactness induces the K-theory restriction map.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.Modules.Complex

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Restriction is exact for the quasi-isomorphism Waldhausen structures. -/
theorem strictRestrict_waldhausenExact :
    Waldhausen.IsExact (strictWaldhausen X).cof (strictWaldhausen X).weq
      (strictWaldhausen U).cof (strictWaldhausen U).weq (strictRestrict j) where
  zero h := (strictRestrict j).map_isZero h
  cofibration f hf := (strictExactRestrict j).map_inflation f hf
  weak f hf := by
    let : QuasiIso f.hom := hf
    exact restrict_quasiIso j f.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (strictPerfect U).ι
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure (CochainComplex X.Modules
      ℤ))
      (strictPerfect X) hi h).map (restrict j)

/-- The canonical open-restriction homomorphism on strict-perfect K-groups. -/
def strictKRestrict (n : ℕ) : StrictK X n →* StrictK U n :=
  Waldhausen.KMap (strictRestrict_waldhausenExact j) n

end Quillen.PerfectComplexes
