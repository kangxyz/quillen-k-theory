/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.GrothendieckComparison

/-! Consumers instantiate the original unequal-universe locally perfect complex
category and literal PerfectK, with its original open restriction. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.Waldhausen.AlgebraicGrothendieck
universe u
namespace Quillen.Tests.PerfectGrothendieckComparison

/-- An arbitrary literal PerfectK₀ class is recovered through its
original Waldhausen presentation. -/
theorem literal_perfect_round_trip (X : Scheme.{u}) (x : PerfectK X 0) :
    perfectGrothendieckKZeroEquiv X ((perfectGrothendieckKZeroEquiv X).symm x) = x :=
  (perfectGrothendieckKZeroEquiv X).apply_symm_apply x

/-- Every actual displayed perfect-complex cofiber gives its difference relation
in the unchanged literal PerfectK₀ group law. -/
theorem original_perfect_cofiber_difference (X : Scheme.{u})
    {A B Q : Perfect X} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (perfectWaldhausen X).cof i)
    (hQ : IsPushout i ((perfectWaldhausen X).isZero.from_ A) q
      ((perfectWaldhausen X).isZero.to_ Q)) :
    (perfectWaldhausen X).kZeroObjectClass B * ((perfectWaldhausen X).kZeroObjectClass A)⁻¹ =
      (perfectWaldhausen X).kZeroObjectClass Q := by
  apply (grothendieckKZeroEquivOfSmallModel (perfectWaldhausen X)).symm.injective
  simp only [map_mul, map_inv, grothendieckKZeroEquivOfSmallModel_symm_objectClass]
  exact congrArg Multiplicative.ofAdd
    ((grading (perfectWaldhausen X)).cofiber_value hi hQ).symm

/-- The original open-restriction kernel is detected on all literal PerfectK₀
classes by the original algebraic restriction map. -/
theorem literal_perfect_restriction_kernel {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (x : PerfectK X 0) :
    perfectKRestrict j 0 x = 1 ↔
      (map (perfectWaldhausen X) (perfectRestrict j)
        (perfectRestrict_waldhausenExact j)).toMultiplicative
          ((perfectGrothendieckKZeroEquiv X).symm x) = 1 := by
  rw [← perfectGrothendieckKZeroEquiv_symm_restrict j x]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    apply (perfectGrothendieckKZeroEquiv U).symm.injective
    simpa only [map_one] using h

end Quillen.Tests.PerfectGrothendieckComparison
