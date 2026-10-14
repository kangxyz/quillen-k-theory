/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.StrictPositiveRetraction
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlasqueBoundedBelowComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.StrictPerfectKEquivalence

/-!
# Original strict-affine to flasque source comparison

This comparison composes only the already proved original strict-affine,
lower-bounded, and flasque inclusion comparisons. The forward source map is
the actual base Godement totalization of the original strict complex.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.PerfectComplexes.ProjectiveLine.StrictPositiveRetraction

/-- The composite is exactly the original affine strict-to-perfect K-map. -/
lemma strictToBoundedBelow_comp_inclusion_KMap (X : Scheme.{u}) (n : ℕ) :
    (Waldhausen.KMap (BoundedBelow.inclusion_exact X) n).comp
      (Waldhausen.KMap (strictToBoundedBelow_exact X) n) = strictToPerfectKMap X n := by
  rw [Waldhausen.KMap_comp_KMap]
  rfl

/-- The literal strict-affine lower-bounded inclusion is a K-bijection in every natural degree. -/
lemma strictToBoundedBelow_KMap_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective (Waldhausen.KMap (strictToBoundedBelow_exact (Spec R)) n) := by
  have hc : Function.Bijective
      ((Waldhausen.KMap (BoundedBelow.inclusion_exact (Spec R)) n).comp
        (Waldhausen.KMap (strictToBoundedBelow_exact (Spec R)) n)) := by
    rw [strictToBoundedBelow_comp_inclusion_KMap]
    exact Affine.strictToPerfectKMap_bijective R n
  have hi := BoundedBelow.inclusion_KMap_bijective (Spec R) n
  constructor
  · intro x y h
    apply hc.1
    change Waldhausen.KMap (BoundedBelow.inclusion_exact (Spec R)) n
      (Waldhausen.KMap (strictToBoundedBelow_exact (Spec R)) n x) =
      Waldhausen.KMap (BoundedBelow.inclusion_exact (Spec R)) n
        (Waldhausen.KMap (strictToBoundedBelow_exact (Spec R)) n y)
    rw [h]
  · intro y
    obtain ⟨x, hx⟩ := hc.2 (Waldhausen.KMap (BoundedBelow.inclusion_exact (Spec R)) n y)
    exact ⟨x, hi.1 hx⟩

/-- The literal base totalization is bijective by its two already proved original weak units. -/
lemma total_KMap_bijective (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (Waldhausen.KMap (FlasqueBoundedBelow.total_exact X) n) :=
  ⟨Function.LeftInverse.injective (FlasqueBoundedBelow.total_KMap_rightInverse X n),
    Function.RightInverse.surjective (FlasqueBoundedBelow.total_KMap_leftInverse X n)⟩

/-- The actual strict-affine to flasque source K-map is a bijection, including degree zero. -/
theorem strictTotal_KMap_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective (Waldhausen.KMap (strictTotal_exact (Spec R)) n) := by
  rw [show Waldhausen.KMap (strictTotal_exact (Spec R)) n =
    (Waldhausen.KMap (FlasqueBoundedBelow.total_exact (Spec R)) n).comp
      (Waldhausen.KMap (strictToBoundedBelow_exact (Spec R)) n) from
    (Waldhausen.KMap_comp_KMap (strictToBoundedBelow_exact (Spec R))
      (FlasqueBoundedBelow.total_exact (Spec R)) n).symm]
  exact (total_KMap_bijective (Spec R) n).comp (strictToBoundedBelow_KMap_bijective R n)

end Quillen.PerfectComplexes.ProjectiveLine.StrictPositiveRetraction
