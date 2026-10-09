import Quillen.KTheory.API
noncomputable section
universe w v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits Quillen

namespace Consumer
variable {C : Type u₁} {D : Type u₂} {T : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} T]
  [Preadditive C] [Preadditive D] [Preadditive T]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts T]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] [EssentiallySmall.{w} T]
  {EC : ExactStructure C} {ED : ExactStructure D} {ET : ExactStructure T}

-- Actual strict laws for chosen small-model K-maps, in a shared small universe.
theorem small_identity_map (E : ExactStructure C) (n : ℕ) :
    (ExactFunctor.id E).smallKMap n = MonoidHom.id (E.SmallK n) :=
  ExactFunctor.smallKMap_id E n

theorem small_composition_map (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) (n : ℕ) :
    (F.comp G).smallKMap n = (G.smallKMap n).comp (F.smallKMap n) :=
  ExactFunctor.smallKMap_comp F G n

theorem small_naturally_isomorphic_maps {F G : ExactFunctor EC ED}
    (e : F.toFunctor ≅ G.toFunctor) (n : ℕ) : F.smallKMap n = G.smallKMap n :=
  ExactFunctor.smallKMap_eq_of_natIso e n
end Consumer
