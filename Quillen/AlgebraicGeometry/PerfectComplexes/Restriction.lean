/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.VectorBundleInclusion
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Restriction

/-!
# Actual open restriction of strict perfect complexes

Restriction is applied termwise to actual sheaf complexes. Its exactness
implies preservation of quasi-isomorphisms. Strict boundedness and finite
local freeness are preserved, giving genuine Waldhausen restriction maps.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory.ExactCategory

open Quillen






noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Strict perfectness survives actual geometric open restriction. -/
theorem strictPerfect_restrict {K : Complex X} (hK : strictPerfect X K) :
    strictPerfect U ((restrict j).obj K) := by
  obtain ⟨⟨a, b, hb⟩, hv⟩ := hK
  refine ⟨⟨a, b, fun n hn ↦ (Scheme.Modules.restrictFunctor j).map_isZero (hb n hn)⟩, ?_⟩
  intro n
  let : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X (K.X n) := hv n
  exact AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_restrict j (K.X n)

/-- The restriction functor on strict perfect complexes. -/
def strictRestrict : StrictPerfect X ⥤ StrictPerfect U :=
  (strictPerfect U).lift ((strictPerfect X).ι ⋙ restrict j)
    (fun K ↦ strictPerfect_restrict j K.property)

instance strictRestrict_additive : (strictRestrict j).Additive := by
  unfold strictRestrict
  infer_instance

/-- Restriction preserves the actual inherited short exact sequences. -/
def strictExactRestrict : CategoryTheory.ExactCategory.ExactFunctor (strictExactStructure X)
  (strictExactStructure U)
  where
  toFunctor := strictRestrict j
  map_conflation S hS := by
    change ((S.map (strictPerfect X).ι).map (restrict j)).ShortExact
    exact hS.map_of_exact _

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
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure (Complex X))
      (strictPerfect X) hi h).map (restrict j)

/-- The canonical open-restriction homomorphism on strict-perfect K-groups. -/
def strictKRestrict (n : ℕ) : StrictK X n →* StrictK U n :=
  Waldhausen.KMap (strictRestrict_waldhausenExact j) n

end Quillen.PerfectComplexes
