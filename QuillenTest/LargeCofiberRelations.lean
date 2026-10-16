/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.LargeCofiberRelations
public import Quillen.AlgebraicGeometry.PerfectComplexes.KTheory

/-!
The original large category of perfect complexes consumes the cofiber relation directly,
without requiring callers to replace their objects, morphisms, or displayed pushout by small
representatives. The quotient class has its explicit source-inverse orientation.
-/
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

@[expose] public section
noncomputable section
open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.PerfectComplexes
universe u
namespace QuillenTest.LargeCofiberRelations

/-- The actual perfect quotient class retains the signed original cofiber equation. -/
theorem perfect_cofiber_class (X : Scheme.{u})
    {A B Q : Perfect X} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (perfectWaldhausen X).cof i)
    (hQ : IsPushout i ((perfectWaldhausen X).isZero.from_ A) q
      ((perfectWaldhausen X).isZero.to_ Q)) :
    (perfectWaldhausen X).kZeroObjectClass Q =
      ((perfectWaldhausen X).kZeroObjectClass A)⁻¹ *
        (perfectWaldhausen X).kZeroObjectClass B := by
  rw [(perfectWaldhausen X).kZeroObjectClass_cofiber_of_large hi hQ]
  simp

/-- The large perfect category also consumes an arbitrary actual cofibration pushout. -/
private theorem perfect_pushout_class (X : Scheme.{u})
    {A B D Q : Perfect X} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ Q} {j : D ⟶ Q}
    (hi : (perfectWaldhausen X).cof i) (hQ : IsPushout i f g j) :
    (perfectWaldhausen X).kZeroObjectClass Q * (perfectWaldhausen X).kZeroObjectClass A =
      (perfectWaldhausen X).kZeroObjectClass B * (perfectWaldhausen X).kZeroObjectClass D := by
  rw [(perfectWaldhausen X).kZeroObjectClass_pushout_of_large hi hQ]
  simp

end QuillenTest.LargeCofiberRelations
