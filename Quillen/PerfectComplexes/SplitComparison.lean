import Quillen.PerfectComplexes.SplitFactorization
import Quillen.Waldhausen.Approximation.SplitKEquivalence

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

@[simp]
theorem splitStrictKEquiv_toMonoidHom (X : Scheme.{u}) (n : ℕ) :
    (splitStrictKEquiv X n).toMonoidHom = splitStrictToStrictKMap X n := rfl

@[simp]
theorem splitPerfectKEquiv_toMonoidHom (X : Scheme.{u}) (n : ℕ) :
    (splitPerfectKEquiv X n).toMonoidHom = splitPerfectToPerfectKMap X n := rfl

end Quillen.PerfectComplexes
