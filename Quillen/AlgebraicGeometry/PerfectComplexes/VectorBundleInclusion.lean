/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Exact
public import Quillen.AlgebraicGeometry.PerfectComplexes.Strict
public import Quillen.Waldhausen.PointedFunctor

/-! # The vector-bundle inclusion on Waldhausen K-theory

The native degree-zero inclusion and inherited exactness come from Aglib. Its
Waldhausen exactness gives the actual S-construction comparison map below.
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

variable (X : Scheme.{u})

/-- The degree-zero inclusion is exact for the actual Waldhausen structures:
vector-bundle isomorphisms map to quasi-isomorphisms, and cofibration pushouts
are preserved. -/
theorem vectorBundleInclusion_waldhausenExact :
    Waldhausen.IsExact
      (Waldhausen.ofExactCategory (AlgebraicGeometry.Scheme.Modules.vectorBundleExactStructure
        X)).cof
      (Waldhausen.ofExactCategory (AlgebraicGeometry.Scheme.Modules.vectorBundleExactStructure
        X)).weq
      (strictWaldhausen X).cof (strictWaldhausen X).weq (vectorBundleInclusion X) where
  zero h := (vectorBundleInclusion X).map_isZero h
  cofibration f hf := (vectorBundleExactInclusion X).map_inflation f hf
  weak f hf := by
    let : IsIso f := hf
    change QuasiIso ((vectorBundleInclusion X).map f).hom
    infer_instance
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (strictPerfect X).ι
    exact (Waldhausen.fullSubcategory_map_pushout
      (AlgebraicGeometry.Scheme.Modules.sheafExactStructure X)
      (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree X) hi h).map
      (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0)

/-- The genuine degree-zero S-construction comparison map. Proving that it
is an isomorphism is Gillet–Waldhausen; comparing its source with `SchemeK`
additionally needs the Quillen Q/S comparison. -/
def vectorBundleSComparison (n : ℕ) :
    (Waldhausen.ofExactCategory (AlgebraicGeometry.Scheme.Modules.vectorBundleExactStructure X)).K n
      →*
      StrictK X n :=
  Waldhausen.KMap (vectorBundleInclusion_waldhausenExact X) n

end Quillen.PerfectComplexes
