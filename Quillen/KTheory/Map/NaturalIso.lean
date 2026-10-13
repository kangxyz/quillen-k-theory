/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.KTheory.Map.Functoriality

/-!
# Natural-isomorphism invariance of canonical K-maps

A natural isomorphism of exact functors lifts to their Q-functors by an
explicit comparison of admissible spans. At the chosen zero objects its
normalization has identity component. The resulting realization homotopy is
therefore based, and proves equality of the original zero-based K-maps.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.ExactFunctor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}
  {F G : ExactFunctor EC ED}

/-- Naturality in Q is obtained by comparing the actual pullback apices of
mapped spans with the component isomorphism at their original apex. -/
theorem mapQ_iso_naturality (e : F.toFunctor ≅ G.toFunctor)
    {X Y : C} (s : Span EC.deflation EC.inflation X Y) :
    F.mapQ.map (Q.mkHom _ _ s) ≫ (ED.qIsoOfIso (e.app Y)).hom =
      (ED.qIsoOfIso (e.app X)).hom ≫ G.mapQ.map (Q.mkHom _ _ s) := by
  let t : Span ED.deflation ED.inflation (F.toFunctor.obj X) (G.toFunctor.obj Y) :=
    { apex := F.toFunctor.obj s.apex
      l := F.toFunctor.map s.l
      r := F.toFunctor.map s.r ≫ (e.app Y).hom
      wl := F.map_deflation _ s.wl
      wr := ED.inflation_comp _ _ (F.map_inflation _ s.wr)
        (ED.inflation_of_iso (e.app Y)) }
  let sq₁ : IsPullback (𝟙 (F.toFunctor.obj s.apex)) (F.toFunctor.map s.r)
      (F.toFunctor.map s.r) (𝟙 (F.toFunctor.obj Y)) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  let sq₂ : IsPullback (F.toFunctor.map s.l) (e.app s.apex).hom
      (e.app X).hom (G.toFunctor.map s.l) :=
    IsPullback.of_vert_isIso ⟨e.hom.naturality s.l⟩
  let : HasPullback (F.toFunctor.map s.r) (𝟙 (F.toFunctor.obj Y)) := sq₁.hasPullback
  let : HasPullback (e.app X).hom (G.toFunctor.map s.l) := sq₂.hasPullback
  have h₁ : Q.mkHom _ _ t =
      F.mapQ.map (Q.mkHom _ _ s) ≫ (ED.qIsoOfIso (e.app Y)).hom := by
    apply Q.mkHom_eq_of_apexIso _ _ _ _ sq₁.isoPullback
    · change sq₁.isoPullback.hom ≫ pullback.fst _ _ ≫ F.toFunctor.map s.l =
        F.toFunctor.map s.l
      simp
    · change sq₁.isoPullback.hom ≫ pullback.snd _ _ ≫ (e.app Y).hom =
        F.toFunctor.map s.r ≫ (e.app Y).hom
      simp
  have h₂ : Q.mkHom _ _ t =
      (ED.qIsoOfIso (e.app X)).hom ≫ G.mapQ.map (Q.mkHom _ _ s) := by
    apply Q.mkHom_eq_of_apexIso _ _ _ _ sq₂.isoPullback
    · change sq₂.isoPullback.hom ≫ pullback.fst _ _ ≫ 𝟙 _ = F.toFunctor.map s.l
      simp
    · change sq₂.isoPullback.hom ≫ pullback.snd _ _ ≫ G.toFunctor.map s.r =
        F.toFunctor.map s.r ≫ (e.app Y).hom
      simp only [IsPullback.isoPullback_hom_snd_assoc]
      exact (e.hom.naturality s.r).symm
  exact h₁.symm.trans h₂

/-- An underlying natural isomorphism of exact functors induces a natural
isomorphism of their genuine Q-functors. -/
def mapQIso (e : F.toFunctor ≅ G.toFunctor) : F.mapQ ≅ G.mapQ :=
  NatIso.ofComponents (fun X => ED.qIsoOfIso (e.app X.obj.of)) (by
    rintro X Y ⟨s⟩
    exact mapQ_iso_naturality e s)

@[simp]
theorem mapQIso_app (e : F.toFunctor ≅ G.toFunctor) (X : C) :
    (mapQIso e).app (Q.of EC.deflation EC.inflation X) = ED.qIsoOfIso (e.app X) := rfl

end Quillen.ExactFunctor

namespace Quillen

section RebaseNaturalIso
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F G : C ⥤ D}

/-- A natural isomorphism compares two independently normalized functors. -/
def rebaseFunctorNatIso (α : F ≅ G) (c : C) (d : D)
    (e : F.obj c ≅ d) (f : G.obj c ≅ d) :
    rebaseFunctor F c d e ≅ rebaseFunctor G c d f :=
  (rebaseFunctorIso F c d e).symm ≪≫ α ≪≫ rebaseFunctorIso G c d f

/-- The source and target of the normalized comparison agree at the base. -/
theorem rebaseFunctorNatIso_obj_base (c : C) (d : D)
    (e : F.obj c ≅ d) (f : G.obj c ≅ d) :
    (rebaseFunctor F c d e).obj c = (rebaseFunctor G c d f).obj c :=
  (rebaseFunctor_obj_base F c d e).trans (rebaseFunctor_obj_base G c d f).symm

/-- A comparison compatible with the supplied base isomorphisms has identity
component after normalization, with all object transports explicit. -/
theorem rebaseFunctorNatIso_hom_base (α : F ≅ G) (c : C) (d : D)
    (e : F.obj c ≅ d) (f : G.obj c ≅ d) (h : α.app c ≪≫ f = e) :
    (rebaseFunctorNatIso α c d e f).hom.app c =
      eqToHom (rebaseFunctorNatIso_obj_base c d e f) := by
  apply (cancel_mono (eqToHom (rebaseFunctor_obj_base G c d f))).mp
  have hh : α.hom.app c ≫ f.hom = e.hom := congrArg Iso.hom h
  have he : e.hom = (rebaseFunctorIso F c d e).hom.app c ≫
      eqToHom (rebaseFunctor_obj_base F c d e) := by
    rw [rebaseFunctorIso_hom_base]
    simp
  dsimp only [rebaseFunctorNatIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [rebaseFunctorIso_hom_base]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [hh, he]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end RebaseNaturalIso

namespace ExactFunctor
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}
  {F G : ExactFunctor EC ED}

/-- The Q comparison respects the canonical zero-object isomorphisms, since
maps to the original zero object are unique. -/
theorem mapQIso_comp_qZeroIso (e : F.toFunctor ≅ G.toFunctor) :
    (mapQIso e).app (Q.of EC.deflation EC.inflation (0 : C)) ≪≫
      ED.qIsoOfIso G.toFunctor.mapZeroObject = ED.qIsoOfIso F.toFunctor.mapZeroObject := by
  rw [mapQIso_app, ← ExactStructure.qIsoOfIso_trans]
  congr 1
  apply Iso.ext
  apply Subsingleton.elim

/-- The natural comparison of the actual zero-normalized Q-functors used in
`KMap`, rather than an unbased comparison of classifying maps. -/
def normalizedQIso (e : F.toFunctor ≅ G.toFunctor) : F.normalizedQ ≅ G.normalizedQ :=
  rebaseFunctorNatIso (mapQIso e) (Q.of EC.deflation EC.inflation (0 : C))
    (Q.of ED.deflation ED.inflation (0 : D))
    (ED.qIsoOfIso F.toFunctor.mapZeroObject) (ED.qIsoOfIso G.toFunctor.mapZeroObject)

/-- Both normalized Q-functors send the source zero to the same target zero. -/
theorem normalizedQIso_obj_base :
    F.normalizedQ.obj (Q.of EC.deflation EC.inflation (0 : C)) =
      G.normalizedQ.obj (Q.of EC.deflation EC.inflation (0 : C)) :=
  rebaseFunctorNatIso_obj_base _ _ _ _

/-- The normalized comparison is the identity at the chosen zero vertex. -/
theorem normalizedQIso_hom_base (e : F.toFunctor ≅ G.toFunctor) :
    (normalizedQIso e).hom.app (Q.of EC.deflation EC.inflation (0 : C)) =
      eqToHom (normalizedQIso_obj_base (F := F) (G := G)) :=
  rebaseFunctorNatIso_hom_base _ _ _ _ _ (mapQIso_comp_qZeroIso e)

/-- Naturally isomorphic exact functors induce the same canonical K-map.
The comparison realizes to a genuine homotopy fixed at the chosen zero point. -/
theorem KMap_eq_of_natIso (e : F.toFunctor ≅ G.toFunctor) (n : ℕ) :
    F.KMap n = G.KMap n := by
  let H := classifyingSpaceNaturalTransformationBasedHomotopy
    (normalizedQIso e).hom (Q.of EC.deflation EC.inflation (0 : C))
    (normalizedQIso_obj_base (F := F) (G := G)) (normalizedQIso_hom_base e)
  have hH : ∀ t, H.toHomotopy (t, EC.kBasepoint) = ED.kBasepoint := by
    intro t
    exact (H.prop t EC.kBasepoint (Set.mem_singleton _)).trans F.normalizedQ_map_point
  exact piMap_eq_of_based_homotopy n F.normalizedQ_map_point G.normalizedQ_map_point
    H.toHomotopy hH

end ExactFunctor
end Quillen
