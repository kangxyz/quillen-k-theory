/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Original colimit maps with successor-interleaving inverses

A natural transformation between sequential diagrams induces an isomorphism on their actual
colimits when specified return maps to the next original source stage satisfy both successor
identities. The inverse is constructed from those maps, and its formula on every original stage
inclusion is retained. No invertibility of the individual stage maps is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Quillen.SequentialInterleaving

variable {C : Type u} [Category.{v} C] {F G : ℕ ⥤ C} (η : F ⟶ G)
  (q : ∀ n, G.obj n ⟶ F.obj (n + 1))
  (hηq : ∀ n, η.app n ≫ q n = F.map (homOfLE (Nat.le_succ n)))
  (hqη : ∀ n, q n ≫ η.app (n + 1) = G.map (homOfLE (Nat.le_succ n)))
  [HasColimit F] [HasColimit G]

/-- The actual return maps give a cocone into the original source colimit. -/
def inverseCocone : Cocone G where
  pt := colimit F
  ι := NatTrans.ofSequence (fun n ↦ q n ≫ colimit.ι F (n + 1)) (by
    intro n
    change G.map (homOfLE (Nat.le_succ n)) ≫ (q (n + 1) ≫ colimit.ι F (n + 1 + 1)) =
      (q n ≫ colimit.ι F (n + 1)) ≫ 𝟙 _
    rw [Category.comp_id, ← hqη, Category.assoc, ← Category.assoc (η.app (n + 1)), hηq,
      colimit.w])

/-- The constructed inverse retains the specified return map at every original stage. -/
def inverse : colimit G ⟶ colimit F :=
  colimit.desc G (inverseCocone η q hηq hqη)

@[reassoc (attr := simp)]
theorem ι_inverse (n : ℕ) :
    colimit.ι G n ≫ inverse η q hηq hqη = q n ≫ colimit.ι F (n + 1) :=
  colimit.ι_desc _ _

/-- The source successor identity gives the original left inverse equation. -/
theorem hom_inverse : colimMap η ≫ inverse η q hηq hqη = 𝟙 (colimit F) := by
  apply colimit.hom_ext
  intro n
  rw [ι_colimMap_assoc, ι_inverse, ← Category.assoc, hηq, colimit.w, Category.comp_id]

/-- The target successor identity gives the original right inverse equation. -/
theorem inverse_hom : inverse η q hηq hqη ≫ colimMap η = 𝟙 (colimit G) := by
  apply colimit.hom_ext
  intro n
  rw [ι_inverse_assoc, ι_colimMap, ← Category.assoc, hqη, colimit.w, Category.comp_id]

/-- The isomorphism has the unchanged induced colimit map as its forward arrow. -/
def colimitIso : colimit F ≅ colimit G where
  hom := colimMap η
  inv := inverse η q hηq hqη
  hom_inv_id := hom_inverse η q hηq hqη
  inv_hom_id := inverse_hom η q hηq hqη

@[simp]
theorem colimitIso_hom : (colimitIso η q hηq hqη).hom = colimMap η := rfl

end Quillen.SequentialInterleaving
