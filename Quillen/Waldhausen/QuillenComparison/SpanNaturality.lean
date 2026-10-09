import Quillen.KTheory.Map.CoherenceData

/-!
# Naturality of admissible-span representatives

Commuting isomorphisms of a span and its endpoints induce the expected
commuting square in the existing Q-category. This is used for the vertical
isomorphism direction of the exact-category S-construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory CategoryTheory.Limits

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)

/-- Isomorphic endpoint-and-apex data give a naturality square of actual
Q-arrows. The proof compares the pullback representatives of both composites. -/
theorem qSpan_iso_naturality {X Y X' Y' : C}
    (s : Span E.deflation E.inflation X Y) (t : Span E.deflation E.inflation X' Y')
    (a : X ≅ X') (b : Y ≅ Y') (c : s.apex ≅ t.apex)
    (hl : s.l ≫ a.hom = c.hom ≫ t.l) (hr : s.r ≫ b.hom = c.hom ≫ t.r) :
    Q.mkHom E.deflation E.inflation s ≫ (E.qIsoOfIso b).hom =
      (E.qIsoOfIso a).hom ≫ Q.mkHom E.deflation E.inflation t := by
  let u : Span E.deflation E.inflation X Y' :=
    { apex := s.apex
      l := s.l
      r := s.r ≫ b.hom
      wl := s.wl
      wr := E.inflation_comp _ _ s.wr (E.inflation_of_iso b) }
  let sq₁ : IsPullback (𝟙 s.apex) s.r s.r (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  let sq₂ : IsPullback s.l c.hom a.hom t.l :=
    IsPullback.of_vert_isIso ⟨hl⟩
  let : HasPullback s.r (𝟙 Y) := sq₁.hasPullback
  let : HasPullback a.hom t.l := sq₂.hasPullback
  have h₁ : Q.mkHom E.deflation E.inflation u =
      Q.mkHom E.deflation E.inflation s ≫ (E.qIsoOfIso b).hom := by
    apply Q.mkHom_eq_of_apexIso _ _ _ _ sq₁.isoPullback
    · change sq₁.isoPullback.hom ≫ pullback.fst _ _ ≫ s.l = s.l
      simp
    · change sq₁.isoPullback.hom ≫ pullback.snd _ _ ≫ b.hom = s.r ≫ b.hom
      simp
  have h₂ : Q.mkHom E.deflation E.inflation u =
      (E.qIsoOfIso a).hom ≫ Q.mkHom E.deflation E.inflation t := by
    apply Q.mkHom_eq_of_apexIso _ _ _ _ sq₂.isoPullback
    · change sq₂.isoPullback.hom ≫ pullback.fst _ _ ≫ 𝟙 _ = s.l
      simp
    · change sq₂.isoPullback.hom ≫ pullback.snd _ _ ≫ t.r = s.r ≫ b.hom
      simpa using hr.symm
  exact h₁.symm.trans h₂

end Quillen.Waldhausen.QuillenComparison
