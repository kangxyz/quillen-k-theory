/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceCoherence

/-! Small-model images of fixed iso words, without unfolding their normalization factors. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
universe u v
namespace Quillen.PerfectComplexes.BassReferenceMerge
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Preserve the literal three-factor word under the existing small-model iso operation. -/
theorem smallIso_trans_three {F₀ F₁ F₂ F₃ : C ⥤ D}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) :
    smallIso (a ≪≫ b ≪≫ c) = smallIso a ≪≫ smallIso b ≪≫ smallIso c := by
  rw [smallIso_trans, smallIso_trans]

/-- Transport a proved three-versus-two reference word while keeping every inner iso opaque. -/
theorem smallIso_word_three_two {F₀ F₁ F₂ F₃ G : C ⥤ D}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃)
    (d : F₀ ≅ G) (e : G ≅ F₃) (h : a ≪≫ b ≪≫ c = d ≪≫ e) :
    smallIso a ≪≫ smallIso b ≪≫ smallIso c = smallIso d ≪≫ smallIso e :=
  (smallIso_trans_three a b c).symm.trans
    ((congrArg smallIso h).trans (smallIso_trans d e))

/-- Group the fixed four-versus-three word before taking its small-model image. -/
theorem smallIso_word_four_three {F₀ F₁ F₂ F₃ F₄ G₁ G₂ : C ⥤ D}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) (d : F₃ ≅ F₄)
    (e : F₀ ≅ G₁) (f : G₁ ≅ G₂) (g : G₂ ≅ F₄)
    (h : (a ≪≫ b) ≪≫ c ≪≫ d = e ≪≫ f ≪≫ g) :
    smallIso a ≪≫ smallIso (b ≪≫ c) ≪≫ smallIso d =
      smallIso (e ≪≫ f) ≪≫ smallIso g := by
  apply smallIso_word_three_two
  simpa only [Iso.trans_assoc] using h

end Quillen.PerfectComplexes.BassReferenceMerge
