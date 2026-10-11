/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.KTheory.GrothendieckComparison.Retraction

/-! Regression properties for the original homotopical-to-classical retraction. -/

@[expose] public section

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits Quillen
namespace Quillen.Tests.GrothendieckRetraction

variable {C D : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
  (E : ExactStructure C) (ED : ExactStructure D)

/-- The sign and multiplication convention recover a genuine difference of classes. -/
theorem object_difference (X Y : C) :
    E.kZeroToGrothendieck (E.kZeroObjectClass X * (E.kZeroObjectClass Y)⁻¹) =
      Multiplicative.ofAdd (E.grothendieckClass X - E.grothendieckClass Y) := by
  simp [sub_eq_add_neg]

/-- Equality of arbitrary classical classes is detected by the original K₀ map. -/
theorem original_comparison_detects_equality (a b : Multiplicative E.GrothendieckGroup) :
    E.grothendieckToKZero a = E.grothendieckToKZero b ↔ a = b :=
  E.grothendieckToKZero_injective.eq_iff

/-- Exact-functor naturality remains compatible with the new retraction on the
proven classical image; this does not assume that the image is all of K₀. -/
theorem naturality_on_classical_image (F : ExactFunctor E ED)
    (a : Multiplicative E.GrothendieckGroup) :
    ED.kZeroToGrothendieck (F.KMap 0 (E.grothendieckToKZero a)) =
      F.grothendieckMap.toMultiplicative a := by
  have h := DFunLike.congr_fun F.grothendieckToKZero_naturality a
  change F.KMap 0 (E.grothendieckToKZero a) =
    ED.grothendieckToKZero (F.grothendieckMap.toMultiplicative a) at h
  rw [h]
  exact DFunLike.congr_fun ED.kZeroToGrothendieck_comp _

/-- The retraction cannot turn an additional topological equality between
canonical object differences into an extra classical relation. -/
theorem object_difference_detects_relation (X Y Z : C)
    (h : E.kZeroObjectClass X * (E.kZeroObjectClass Y)⁻¹ = E.kZeroObjectClass Z) :
    E.grothendieckClass X - E.grothendieckClass Y = E.grothendieckClass Z := by
  apply Multiplicative.ofAdd.injective
  have he := congrArg E.kZeroToGrothendieck h
  simpa [sub_eq_add_neg] using he

/-- The generic theorem reflects equalities of original completed loops in
arbitrary categories, with no exact-category or commutativity hypothesis. -/
theorem completed_loop_equality {A : Type u} [Category.{v} A] (a : A)
    (p q : End ((⊤ : MorphismProperty A).Q.obj a))
    (h : classifyingGroupoidCompletionMap A a p = classifyingGroupoidCompletionMap A a q) :
    p = q :=
  classifyingGroupoidCompletionMap_injective A a h

end Quillen.Tests.GrothendieckRetraction
