/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Quillen.KTheory.Map.NaturalIso

/-!
# Functoriality of small-model K-theory

The chosen small-model equivalences provide natural identity and composition
comparisons. Natural-isomorphism invariance of the zero-normalized K-map
turns these comparisons into strict identity and composition laws on SmallK.
No comparison with an out-of-universe realization is required.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe w v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits

namespace Quillen.ExactFunctor

variable {C : Type u₁} {D : Type u₂} {T : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} T]
  [Preadditive C] [Preadditive D] [Preadditive T]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts T]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] [EssentiallySmall.{w} T]
  {EC : ExactStructure C} {ED : ExactStructure D} {ET : ExactStructure T}

/-- The identity on an exact category descends to the identity on its small
model up to the counit of the actual chosen equivalence. -/
def smallModelIdIso (E : ExactStructure C) :
    (ExactFunctor.id E).smallModel.toFunctor ≅
      (ExactFunctor.id E.smallModel).toFunctor :=
  Functor.isoWhiskerRight (Functor.rightUnitor (equivSmallModel.{w} C).inverse)
    (equivSmallModel.{w} C).functor ≪≫ (equivSmallModel.{w} C).counitIso

/-- The unit of the intermediate small-model equivalence is the canonical
comparison between a descended composite and the composite of descents. -/
def smallModelCompIso (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) :
    (F.comp G).smallModel.toFunctor ≅ (F.smallModel.comp G.smallModel).toFunctor :=
  NatIso.ofComponents (fun X =>
    (equivSmallModel.{w} T).functor.mapIso (G.toFunctor.mapIso
      ((equivSmallModel.{w} D).unitIso.app
        (F.toFunctor.obj ((equivSmallModel.{w} C).inverse.obj X))))) (by
    intro X Y f
    change (equivSmallModel.{w} T).functor.map
        (G.toFunctor.map (F.toFunctor.map ((equivSmallModel.{w} C).inverse.map f))) ≫
        (equivSmallModel.{w} T).functor.map
          (G.toFunctor.map ((equivSmallModel.{w} D).unitIso.hom.app _)) =
      (equivSmallModel.{w} T).functor.map
        (G.toFunctor.map ((equivSmallModel.{w} D).unitIso.hom.app _)) ≫
        (equivSmallModel.{w} T).functor.map (G.toFunctor.map
          ((equivSmallModel.{w} D).inverse.map ((equivSmallModel.{w} D).functor.map
            (F.toFunctor.map ((equivSmallModel.{w} C).inverse.map f)))))
    simp only [← Functor.map_comp]
    exact congrArg (fun k => (equivSmallModel.{w} T).functor.map (G.toFunctor.map k))
      ((equivSmallModel.{w} D).unitIso.hom.naturality
        (F.toFunctor.map ((equivSmallModel.{w} C).inverse.map f))))

/-- Natural isomorphisms also descend through the chosen small models. -/
def smallModelNatIso {F G : ExactFunctor EC ED} (e : F.toFunctor ≅ G.toFunctor) :
    F.smallModel.toFunctor ≅ G.smallModel.toFunctor :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (equivSmallModel.{w} C).inverse e)
    (equivSmallModel.{w} D).functor

/-- The actual small-model K-map is invariant under underlying natural
isomorphisms, even when the original categories have different universes. -/
theorem smallKMap_eq_of_natIso {F G : ExactFunctor EC ED}
    (e : F.toFunctor ≅ G.toFunctor) (n : ℕ) : F.smallKMap n = G.smallKMap n :=
  KMap_eq_of_natIso (smallModelNatIso e) n

/-- Small-model K-theory preserves identity exact functors. -/
@[simp]
theorem smallKMap_id (E : ExactStructure C) (n : ℕ) :
    (ExactFunctor.id E).smallKMap n = MonoidHom.id (E.SmallK n) := by
  exact (KMap_eq_of_natIso (smallModelIdIso E) n).trans (KMap_id E.smallModel n)

/-- Small-model K-theory preserves composition of actual exact functors. -/
@[simp]
theorem smallKMap_comp (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) (n : ℕ) :
    (F.comp G).smallKMap n = (G.smallKMap n).comp (F.smallKMap n) := by
  exact (KMap_eq_of_natIso (smallModelCompIso F G) n).trans
    (KMap_comp F.smallModel G.smallModel n)

end Quillen.ExactFunctor
