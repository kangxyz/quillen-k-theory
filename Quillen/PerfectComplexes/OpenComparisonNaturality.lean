/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.OpenComparison

/-!
# Literal original absolute/relative comparison squares

On every scheme and in every connective degree, original strict-to-perfect
relative comparison commutes with both original restriction endpoints and
the actual change of weak equivalences. The original functors and canonical
K-maps are retained; the proofs use their literal composition laws.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Original relative comparison commutes with the literal original
restriction endpoints in every degree, on every scheme. -/
lemma perfectOpenKRestrict_comp_strictToPerfectOpenKMap (n : ℕ) :
    (perfectOpenKRestrict j n).comp (strictToPerfectOpenKMap j n) =
      (strictToPerfectKMap U n).comp (StrictOpenWeakImage.relativeKRestrict j n) := by
  unfold perfectOpenKRestrict strictToPerfectOpenKMap StrictOpenWeakImage.relativeKRestrict
    strictToPerfectKMap Waldhausen.subcategoryKMap
  rw [← Waldhausen.KMap_comp, ← Waldhausen.KMap_comp]

/-- The actual absolute and relative comparison maps also commute with the
original change of weak equivalences. -/
lemma strictToPerfectOpenKMap_comp_changeWeak (n : ℕ) :
    (strictToPerfectOpenKMap j n).comp
      (Waldhausen.KMap (Waldhausen.Fibration.changeWeak_exact (StrictOpenWeakImage.nested j)) n) =
      (perfectOpenKMap j n).comp (strictToPerfectKMap X n) := by
  unfold strictToPerfectOpenKMap perfectOpenKMap strictToPerfectKMap Waldhausen.subcategoryKMap
  rw [← Waldhausen.KMap_comp, ← Waldhausen.KMap_comp]

end Quillen.PerfectComplexes
