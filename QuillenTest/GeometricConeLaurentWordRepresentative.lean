/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.GeometricConeLaurentWordRepresentative

/-! Regression laws retaining the literal triple word and the original full power casts. -/
public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.KTheory.Bass.GeometricConeInterchange
open Quillen.KTheory.Bass.GeometricConeFixedWords
universe u w
namespace QuillenTest.GeometricConeLaurentWordRepresentative

/-- The third original word has this explicit execution order on its Laurent representatives. -/
theorem triple_word_representative
    (F : Scheme.{u}ᵒᵖ ⥤ Quillen.LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    laurentInclusion 3 F X ≫ (wordAt 3 F).hom.app X =
      F.map (laurentSwapMap (laurent.op.obj X) ≫
        laurent.op.map (laurentSwapMap X) ≫ laurentSwapMap (laurent.op.obj X)) ≫
          laurentInclusion 3 F X := by
  simpa [laurentReversalMap, laurentInsertionMap, laurentIterate, Category.assoc] using
    laurentInclusion_wordAt 3 F X

/-- Inverse word transport recovers the representative with its original complete power cast. -/
theorem inverse_word_recovers_casted_representative (n : ℕ)
    (F : Scheme.{u}ᵒᵖ ⥤ Quillen.LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    F.map (laurentReversalMap n X) ≫ powerLaurentInclusion n F X ≫
        (eqToHom (power_obj n F)).app X ≫ (wordAt n F).inv.app X =
      powerLaurentInclusion n F X ≫ (eqToHom (power_obj n F)).app X := by
  have h := congrArg (fun f => f ≫ (wordAt n F).inv.app X)
    (powerLaurentInclusion_wordAt n F X)
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using h.symm

end QuillenTest.GeometricConeLaurentWordRepresentative
