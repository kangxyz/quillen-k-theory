/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SplitFactorization
public import Quillen.Waldhausen.Approximation.SplitKEquivalence

/-!
# Genuine change-of-cofibrations equivalences for perfect complexes

The previously constructed canonical comparison maps, from globally
termwise-split cofibrations to ambient monomorphisms with perfect quotient,
are bijective on all connective K-groups. Actual quasi-isomorphisms are
retained throughout. Closure under the explicit mapping cones is proved,
so no approximation or comparison equivalence is an input.

This compares the two cofibration conventions on the same actual object
categories. It does not identify strict-perfect with locally-perfect
K-theory, nor impose uniform Tor-amplitude on non-quasi-compact schemes.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Quillen.PerfectComplexes

/-- The existing strict-perfect change-of-cofibrations map is bijective. -/
theorem splitStrictToStrictKMap_bijective (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (splitStrictToStrictKMap X n) :=
  Waldhausen.splitComplexSubcategoryKMap_bijective (strictPerfect X)
    (fun hK hL f ↦ strictPerfect_mappingCone hK hL f) n

/-- The existing locally-perfect change-of-cofibrations map is bijective. -/
theorem splitPerfectToPerfectKMap_bijective (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (splitPerfectToPerfectKMap X n) :=
  Waldhausen.splitComplexSubcategoryKMap_bijective (locallyPerfect X)
    (fun hK hL f ↦ locallyPerfect_mappingCone hK hL f) n

/-- The canonical equivalence for the two strict-perfect cofibration conventions. -/
def splitStrictKEquiv (X : Scheme.{u}) (n : ℕ) : SplitStrictK X n ≃* StrictK X n :=
  MulEquiv.ofBijective (splitStrictToStrictKMap X n) (splitStrictToStrictKMap_bijective X n)

/-- The canonical equivalence for the two locally-perfect cofibration conventions. -/
def splitPerfectKEquiv (X : Scheme.{u}) (n : ℕ) : SplitPerfectK X n ≃* PerfectK X n :=
  MulEquiv.ofBijective (splitPerfectToPerfectKMap X n) (splitPerfectToPerfectKMap_bijective X n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem splitStrictKEquiv_coe (X : Scheme.{u}) (n : ℕ) :
    ↑(splitStrictKEquiv X n) = splitStrictToStrictKMap X n := rfl

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem splitPerfectKEquiv_coe (X : Scheme.{u}) (n : ℕ) :
    ↑(splitPerfectKEquiv X n) = splitPerfectToPerfectKMap X n := rfl

end Quillen.PerfectComplexes
