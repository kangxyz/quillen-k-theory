/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Restriction


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Extension
public import Quillen.AlgebraicGeometry.PerfectComplexes.VectorBundleInclusion
public import Quillen.Waldhausen.SubcategoryInclusion

/-!
# Connective Waldhausen K-theory of locally perfect complexes

The objects are the actual locally perfect sheaf complexes. Their extension
closure has been proved geometrically. Cofibrations are ambient monomorphisms
whose quotient is locally perfect; weak equivalences are actual
quasi-isomorphisms. All Waldhausen axioms are derived by the full-subcategory
adapter, and K is the genuine S-construction realization's shifted homotopy.

This construction does not prove Q/S, Gillet–Waldhausen, or strict-versus-local
comparison equivalences. It is connective only. For arbitrary non-quasi-compact
schemes, TT's uniform global Tor-amplitude convention is an additional scope
issue; the object predicate here is explicitly local perfectness.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open CategoryTheory.ExactCategory


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- The actual Waldhausen category of locally perfect sheaf complexes. -/
def perfectWaldhausen (X : Scheme.{u}) : Waldhausen.Structure (Perfect X) :=
  Waldhausen.complexSubcategory (locallyPerfect X)

/-- Connective K-groups of the actual locally perfect complex category,
formed using quasi-isomorphism arrows in the S-construction. -/
abbrev PerfectK (X : Scheme.{u}) (n : ℕ) := (perfectWaldhausen X).K n

/-- The actual canonical comparison map from strict-perfect K-groups to
locally perfect K-groups. No equivalence is asserted. -/
def strictToPerfectKMap (X : Scheme.{u}) (n : ℕ) : StrictK X n →* PerfectK X n :=
  Waldhausen.subcategoryKMap (strictPerfect X) (locallyPerfect X)
    (fun _ h ↦ locallyPerfect_of_strictPerfect h) n

/-- The degree-zero vector-bundle S-construction comparison, now landing in
locally perfect K-theory. Comparing its source to Quillen Scheme.K still
requires the separate Q/S comparison theorem. -/
def vectorBundleToPerfectSMap (X : Scheme.{u}) (n : ℕ) :
    (Waldhausen.ofExactCategory (AlgebraicGeometry.Scheme.Modules.vectorBundleExactStructure X)).K n
      →* PerfectK X n :=
  (strictToPerfectKMap X n).comp (vectorBundleSComparison X n)

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual open restriction is Waldhausen-exact for locally perfect complexes. -/
theorem perfectRestrict_waldhausenExact :
    Waldhausen.IsExact (perfectWaldhausen X).cof (perfectWaldhausen X).weq
      (perfectWaldhausen U).cof (perfectWaldhausen U).weq (perfectRestrict j) where
  zero h := (perfectRestrict j).map_isZero h
  cofibration f hf := (perfectExactRestrict j).map_inflation f hf
  weak f hf := by
    let : QuasiIso f.hom := hf
    exact restrict_quasiIso j f.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (locallyPerfect U).ι
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure
      (CochainComplex X.Modules ℤ))
      (locallyPerfect X) hi h).map (restrict j)

/-- The genuine restriction homomorphism on locally perfect K-groups. -/
def perfectKRestrict (n : ℕ) : PerfectK X n →* PerfectK U n :=
  Waldhausen.KMap (perfectRestrict_waldhausenExact j) n

end Quillen.PerfectComplexes
