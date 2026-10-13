/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Strict
public import Quillen.Waldhausen.PointedFunctor

/-!
# The degree-zero vector-bundle comparison map

The inclusion sends a vector bundle to its degree-zero complex. We prove
that it preserves all ambient exact sequences and is Waldhausen-exact. It
therefore gives a genuine S-construction K-map. Neither the Quillen Q/S
comparison nor the Gillet–Waldhausen equivalence is asserted here.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

variable (X : Scheme.{u})

/-- The actual inherited exact structure on strict perfect complexes. -/
abbrev strictExactStructure : Quillen.ExactStructure (StrictPerfect X) :=
  ExactSubcategory.exactStructure (abelianExactStructure (Complex X)) (strictPerfect X)

instance vectorBundleInclusion_additive : (vectorBundleInclusion X).Additive := by
  unfold vectorBundleInclusion
  infer_instance

/-- Placing vector bundles in degree zero preserves every ambient conflation,
including sequences which split only locally. -/
def vectorBundleExactInclusion :
    Quillen.ExactFunctor (SchemeSheaf.vectorBundleExactStructure X) (strictExactStructure X) where
  toFunctor := vectorBundleInclusion X
  map_conflation S hS := by
    have hs : (S.map (SchemeSheaf.finiteLocallyFree X).ι).ShortExact := hS
    let := hs.mono_f
    let := hs.epi_g
    exact hs.map (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0)

/-- The degree-zero inclusion is exact for the actual Waldhausen structures:
vector-bundle isomorphisms map to quasi-isomorphisms, and cofibration pushouts
are preserved. -/
theorem vectorBundleInclusion_waldhausenExact :
    Waldhausen.IsExact
      (Waldhausen.ofExactCategory (SchemeSheaf.vectorBundleExactStructure X)).cof
      (Waldhausen.ofExactCategory (SchemeSheaf.vectorBundleExactStructure X)).weq
      (strictWaldhausen X).cof (strictWaldhausen X).weq (vectorBundleInclusion X) where
  zero h := (vectorBundleInclusion X).map_isZero h
  cofibration f hf := (vectorBundleExactInclusion X).map_inflation f hf
  weak f hf := by
    let : IsIso f := hf
    change QuasiIso ((vectorBundleInclusion X).map f).hom
    infer_instance
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (strictPerfect X).ι
    exact (Waldhausen.fullSubcategory_map_pushout (SchemeSheaf.sheafExactStructure X)
      (SchemeSheaf.finiteLocallyFree X) hi h).map
      (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0)

/-- The genuine degree-zero S-construction comparison map. Proving that it
is an isomorphism is Gillet–Waldhausen; comparing its source with `SchemeK`
additionally needs the Quillen Q/S comparison. -/
def vectorBundleSComparison (n : ℕ) :
    (Waldhausen.ofExactCategory (SchemeSheaf.vectorBundleExactStructure X)).K n →*
      StrictK X n :=
  Waldhausen.KMap (vectorBundleInclusion_waldhausenExact X) n

end Quillen.PerfectComplexes
