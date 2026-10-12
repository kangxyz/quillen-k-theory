/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.GrothendieckComparison

/-!
# Original derived pullback on perfect-complex Grothendieck groups

The homomorphism transports the existing `perfectKPullback` through the genuine
original Grothendieck comparisons. It is not an assertion of an exact raw
perfect pullback functor. Its bounded-flat formula retains the actual geometric
pullback on representatives, without a flatness assumption on the scheme map.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.AlgebraicGrothendieck
universe u
namespace Quillen.PerfectComplexes

/-- Transport of the actual derived K-zero pullback through the original comparisons. -/
def perfectGrothendieckPullback {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) : Group (perfectWaldhausen Y) →+ Group (perfectWaldhausen X) :=
  ((perfectGrothendieckKZeroEquiv X).symm.toMonoidHom.comp
    ((perfectKPullback f 0).comp (perfectGrothendieckKZeroEquiv Y).toMonoidHom)).toAdditive

/-- The original comparison square holds on every original algebraic class. -/
theorem perfectGrothendieckPullback_comparison {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) (x : Group (perfectWaldhausen Y)) :
    perfectGrothendieckKZeroEquiv X (Multiplicative.ofAdd (perfectGrothendieckPullback f x)) =
      perfectKPullback f 0 (perfectGrothendieckKZeroEquiv Y (Multiplicative.ofAdd x)) :=
  (perfectGrothendieckKZeroEquiv X).apply_symm_apply _

/-- Composition retains the original derived K-map composition, with its contravariant order. -/
theorem perfectGrothendieckPullback_comp {X Y Z : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] [CompactSpace Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
    perfectGrothendieckPullback (f ≫ g) =
      (perfectGrothendieckPullback f).comp (perfectGrothendieckPullback g) := by
  apply AddMonoidHom.ext
  intro x
  apply (perfectGrothendieckKZeroEquiv X).injective
  change perfectGrothendieckKZeroEquiv X
      (Multiplicative.ofAdd (perfectGrothendieckPullback (f ≫ g) x)) =
    perfectGrothendieckKZeroEquiv X
      (Multiplicative.ofAdd (perfectGrothendieckPullback f (perfectGrothendieckPullback g x)))
  rw [perfectGrothendieckPullback_comparison, perfectGrothendieckPullback_comparison,
    perfectGrothendieckPullback_comparison, perfectKPullback_comp]
  rfl

/-- On an actual open immersion this is the unchanged original algebraic restriction map. -/
theorem perfectGrothendieckPullback_restrict {U X : Scheme.{u}}
    [CompactSpace U] [CompactSpace X] (j : U ⟶ X) [IsOpenImmersion j] :
    perfectGrothendieckPullback j =
      map (perfectWaldhausen X) (perfectRestrict j) (perfectRestrict_waldhausenExact j) := by
  apply AddMonoidHom.ext
  intro x
  apply (perfectGrothendieckKZeroEquiv U).injective
  change perfectGrothendieckKZeroEquiv U
    (Multiplicative.ofAdd (perfectGrothendieckPullback j x)) = _
  rw [perfectGrothendieckPullback_comparison, perfectKPullback_eq_restrict]
  exact perfectGrothendieckKZeroEquiv_restrict j (Multiplicative.ofAdd x)

/-- An original bounded-flat representative is pulled back by the genuine termwise functor. -/
theorem perfectGrothendieckPullback_boundedFlat_objectClass {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) (K : BoundedFlatPerfect Y) :
    perfectGrothendieckPullback f
      (objectClass (perfectWaldhausen Y) ((boundedFlatPerfectInclusion Y).obj K)) =
    objectClass (perfectWaldhausen X)
      ((boundedFlatPerfectInclusion X).obj ((boundedFlatPerfectPullback f).obj K)) := by
  apply (perfectGrothendieckKZeroEquiv X).injective
  change perfectGrothendieckKZeroEquiv X
      (Multiplicative.ofAdd (perfectGrothendieckPullback f
        (objectClass (perfectWaldhausen Y) ((boundedFlatPerfectInclusion Y).obj K)))) =
    perfectGrothendieckKZeroEquiv X
      (Multiplicative.ofAdd (objectClass (perfectWaldhausen X)
        ((boundedFlatPerfectInclusion X).obj ((boundedFlatPerfectPullback f).obj K))))
  rw [perfectGrothendieckPullback_comparison, perfectGrothendieckKZeroEquiv_objectClass,
    perfectGrothendieckKZeroEquiv_objectClass]
  have h := DFunLike.congr_fun (perfectKPullback_comp_boundedFlat f 0)
    ((boundedFlatPerfectWaldhausen Y).kZeroObjectClass K)
  change perfectKPullback f 0
      (KMap (boundedFlatPerfectInclusion_exact Y) 0
        ((boundedFlatPerfectWaldhausen Y).kZeroObjectClass K)) =
    KMap (boundedFlatPerfectInclusion_exact X) 0
      (KMap (boundedFlatPerfectPullback_exact f) 0
        ((boundedFlatPerfectWaldhausen Y).kZeroObjectClass K)) at h
  rw [KMap_kZeroObjectClass, KMap_kZeroObjectClass, KMap_kZeroObjectClass] at h
  exact h

end Quillen.PerfectComplexes
