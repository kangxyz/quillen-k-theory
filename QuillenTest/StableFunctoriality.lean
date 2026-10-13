/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.SConstruction.Iterated.StableFunctoriality

/-!
Original exact-functor stable maps and original K0 normalization without a zero-image equality.
-/
@[expose] public section

noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u v
namespace QuillenTest.StableFunctoriality

open Quillen
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (W : Structure C) (V : Structure D) (U : Structure E)
  {F G : C ⥤ D} (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)

/-- The original identity map is retained in every integer degree. -/
theorem original_identity (d : ℤ) : exactStableKMap W W (IsExact.id _ _) d = 𝟙 _ :=
  exactStableKMap_id W d

/-- Binary composition gives a literal equality on the genuine stable groups. -/
theorem original_composition {J : D ⥤ E} (hJ : IsExact V.cof V.weq U.cof U.weq J) (d : ℤ) :
    exactStableKMap W U (hF.comp hJ) d = exactStableKMap W V hF d ≫ exactStableKMap V U hJ d :=
  exactStableKMap_comp W V U hF hJ d

/-- Actual pointwise weak natural transformations identify the original stable maps. -/
theorem weak_transformation (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) (d : ℤ) :
    exactStableKMap W V hF d = exactStableKMap W V hG d :=
  exactStableKMap_weakNatTrans W V hF hG η hη d

/-- Natural isomorphisms are accepted without a strict chosen-zero equation. -/
theorem original_iso (e : F ≅ G) (d : ℤ) :
    exactStableKMap W V hF d = exactStableKMap W V hG d := exactStableKMap_iso W V hF hG e d

/-- The normalization preserves the actual old K0 map and actual multiplication. -/
theorem original_Kzero (a : W.K 0) :
    originalKStableEquiv V 0 (Additive.ofMul (KMap hF 0 a)) =
      exactStableKMap W V hF 0 (originalKStableEquiv W 0 (Additive.ofMul a)) :=
  originalKStableEquiv_exact_naturality W V hF 0 a

/-- Every original nonnegative K-map, including K0, controls stable equivalence. -/
theorem original_equivalence_criterion :
    IsStableEquivalence (exactOriginalPrespectrumMap W V hF) ↔
      ∀ n : ℕ, Function.Bijective (KMap hF n) :=
  exactOriginalPrespectrumMap_isStableEquivalence_iff W V hF

/-- Complete weak equivalences at the actual levels suffice without Omega hypotheses. -/
theorem levelwise_stable {P Q : LoopPrespectrum.{u}} (f : P ⟶ Q)
    (hf : ∀ n, IsWeakHomotopyEquivalence (f.map n)) : IsStableEquivalence f :=
  isStableEquivalence_of_levelwise f hf

end QuillenTest.StableFunctoriality
