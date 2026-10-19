/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.Functoriality
public import Quillen.Waldhausen.SmallModel.Basic

/-!
# Original small-model transport on both S-directions

Actual quotient-row postcomposition transports the double S-construction to the original small
model even when the original object and morphism universes differ. The genuine one-step row and
its suspension cylinder are preserved with the original chosen zero, without a universe-equality
assumption on the source category.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory
open Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u v
namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Original small-model postcomposition on every actual quotient-row S-space. -/
def smallModelDoubleMap : doubleS W ⟶ doubleS W.smallModel where
  app n := {
    app m := ↾fun A => ⟨A.val ⋙
      QuotientRows.postcompose W W.smallModel W.smallModel_up_exact n.unop,
      A.property.postcomp
        (QuotientRows.postcompose_exact W W.smallModel W.smallModel_up_exact n.unop)⟩
    naturality m l α := by
      ext A : 3
      apply Subtype.ext
      apply CategoryTheory.Functor.ext (fun _ => rfl) }
  naturality n m α := by
    ext k A : 4
    apply Subtype.ext
    apply CategoryTheory.Functor.ext (fun _ => rfl)

/-- The diagonal map retains both original row directions. -/
def smallModelDoubleDiagonalMap : doubleDiagonal W ⟶ doubleDiagonal W.smallModel :=
  TheoremA.diagonalMap (smallModelDoubleMap W)

/-- The original small-model functor takes the whole suspension row to the same original row. -/
theorem smallModel_suspensionRow {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    suspensionRow W τ ⋙ QuotientRows.postcompose W W.smallModel W.smallModel_up_exact n =
      AsSmall.up ⋙ suspensionRow W.smallModel τ := by
  change (QuotientRows.oneEmbedding W ⋙ QuotientRows.reindex W τ) ⋙ _ = _
  rw [Functor.assoc, ← QuotientRows.postcompose_reindex W W.smallModel W.smallModel_up_exact τ,
    ← Functor.assoc,
    QuotientRows.oneEmbedding_postcompose W W.smallModel W.smallModel_up_exact rfl]
  rfl

/-- The entire first-row cylinder survives original small-model transport in both directions. -/
theorem smallModel_suspensionCylinder :
    (W.smallModelSSetIso.hom ▷ Δ[1]) ≫ suspensionCylinder W.smallModel =
      suspensionCylinder W ≫ W.smallModelDoubleDiagonalMap := by
  ext n z : 4
  apply Subtype.ext
  change z.1.val ⋙ AsSmall.up ⋙ suspensionRow W.smallModel z.2.down =
    z.1.val ⋙ suspensionRow W z.2.down ⋙
      QuotientRows.postcompose W W.smallModel W.smallModel_up_exact n.unop
  rw [W.smallModel_suspensionRow]

end Quillen.Waldhausen.Structure
