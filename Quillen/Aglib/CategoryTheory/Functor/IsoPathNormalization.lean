/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation

/-!
# Independent normalizations of paths and faces

Every edge uses its specified isomorphism. The face is transported by the two actual path
isomorphisms, with no compatibility assumption on the independently chosen normalizations.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃
namespace CategoryTheory.Functor
variable {C₀ : Type u₀} [Category.{v₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]

/-- Normalize the two edges of a path in their original order. -/
def pathNormalization {F F' : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₂}
    (nF : F ≅ F') (nG : G ≅ G') : F ⋙ G ≅ F' ⋙ G' :=
  isoWhiskerRight nF G ≪≫ isoWhiskerLeft F' nG

/-- Transport a whole face by its independently specified source and target path isomorphisms. -/
def faceNormalization {F F' : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₂}
    {H H' : C₀ ⥤ C₃} {I I' : C₃ ⥤ C₂}
    (s : F ⋙ G ≅ H ⋙ I) (nF : F ≅ F') (nG : G ≅ G')
    (nH : H ≅ H') (nI : I ≅ I') : F' ⋙ G' ≅ H' ⋙ I' :=
  (pathNormalization nF nG).symm ≪≫ s ≪≫ pathNormalization nH nI

/-- Whiskering exchange preserves the complete specified path isomorphism. -/
theorem pathNormalization_eq_alternate {F F' : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₂}
    (nF : F ≅ F') (nG : G ≅ G') :
    pathNormalization nF nG = isoWhiskerLeft F nG ≪≫ isoWhiskerRight nF G' := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact nG.hom.naturality (nF.hom.app X)

/-- The inverse path retains the independent edge order used by geometric normalization. -/
theorem pathNormalization_symm_eq_alternate
    {F F' : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₂} (nF : F ≅ F') (nG : G ≅ G') :
    (pathNormalization nF nG).symm =
      isoWhiskerRight nF.symm G' ≪≫ isoWhiskerLeft F nG.symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact (nG.inv.naturality (nF.inv.app X)).symm

/-- An alternate geometric conjugation word is exactly the same normalized face. -/
theorem faceNormalization_eq_alternate
    {F F' : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₂}
    {H H' : C₀ ⥤ C₃} {I I' : C₃ ⥤ C₂}
    (s : F ⋙ G ≅ H ⋙ I) (nF : F ≅ F') (nG : G ≅ G')
    (nH : H ≅ H') (nI : I ≅ I') :
    faceNormalization s nF nG nH nI =
      isoWhiskerRight nF.symm G' ≪≫ isoWhiskerLeft F nG.symm ≪≫ s ≪≫
        isoWhiskerLeft H nI ≪≫ isoWhiskerRight nH I' := by
  rw [faceNormalization, pathNormalization_symm_eq_alternate,
    pathNormalization_eq_alternate]
  simp only [Iso.trans_assoc]

end CategoryTheory.Functor
