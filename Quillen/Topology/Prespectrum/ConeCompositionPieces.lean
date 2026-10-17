/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.ConeSquareMapComposition

/-! The three literal native pieces underlying the original cone reassociation correction. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.ConeCompositionPieces
variable {E F E' F' E'' F'' : LoopPrespectrum.{u}}
  {f : E ⟶ F} {g : E' ⟶ F'} (h : E'' ⟶ F'')
  (a : E ⟶ E') {b : F ⟶ F'} (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))

/-- The first original square track followed by the final Laurent inclusion. -/
abbrev first := H.postcomp (d ≫ mappingConeInclusion h)

/-- The second original square track, with its original associativity endpoint casts. -/
def second : Homotopy ((a ≫ g) ≫ (d ≫ mappingConeInclusion h))
    ((a ≫ c) ≫ (h ≫ mappingConeInclusion h)) :=
  (Homotopy.precomp a (K.postcomp (mappingConeInclusion h))).cast
    (by simp only [Category.assoc]) (by simp only [Category.assoc])

/-- The full final polynomial cylinder; its parameter is not paused or reparametrized. -/
abbrev third := Homotopy.precomp (a ≫ c) (mappingConeHomotopy h)

/-- Exactly the source-level identification used by the original correction's ofLevels. -/
theorem source_level (n : ℕ) :
    (mappingConeSquareNullHomotopy f h (a ≫ c) (b ≫ d)
      (coneSquarePastedHomotopy f g h a b c d H K)).level n =
    (((first h a d H).trans (second h a c d K)).trans (third h a c)).level n := by
  apply Homotopy.trans_level_congr
  · change (((H.postcomp d).trans ((Homotopy.precomp a K).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)).postcomp
        (mappingConeInclusion h)).level n = _
    rw [Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr <;> rfl
  · rfl

end Quillen.LoopPrespectrum.ConeCompositionPieces
