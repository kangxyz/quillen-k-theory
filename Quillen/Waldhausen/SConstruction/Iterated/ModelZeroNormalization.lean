/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumZeroNaturality

/-!
# Weak selected-zero maps through actual evaluation comparisons

The map from the original chosen zero is defined independently of any equivalence. An actual
comparison isomorphism and an explicit evaluation counit transport a known weak zero map to it.
The equivalence is used only to prove weakness, never to replace the target Model arrow.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
universe u
namespace Quillen.Waldhausen.IteratedS.ModelZeroNormalization

/-- The unique map from the actual chosen zero to the unchanged target Model arrow. -/
def zeroToMap {V W : Model.{u}} (F : V ⟶ W) :
    (zeroHom V W).functor ⟶ F.functor where
  app X := W.waldhausen.isZero.to_ (F.functor.obj X)
  naturality _ _ _ := W.waldhausen.isZero.eq_of_src _ _

/-- A known weak zero map and an actual evaluation counit prove the independent raw map weak. -/
theorem zeroToMap_weak_of_comparison {V W U T : Model.{u}}
    (F : V ⟶ W) (G : U ⟶ T) (a : V ⟶ U) (b : W ⟶ T)
    (α : (F ≫ b).functor ≅ (a ≫ G).functor)
    (η : (zeroHom V W).functor ⟶ F.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (d : U ⥤ V) (ε : d ⋙ a.functor ≅ 𝟭 U) (Y : U) :
    T.waldhausen.weq ((zeroToMap G).app Y) := by
  have hX (X : V) : T.waldhausen.weq ((zeroToMap G).app (a.functor.obj X)) := by
    have he : (zeroToMap G).app (a.functor.obj X) =
        eqToHom b.zero.symm ≫ b.functor.map (η.app X) ≫ α.hom.app X :=
      T.waldhausen.isZero.eq_of_src _ _
    rw [he]
    exact T.waldhausen.weq.comp_mem _ _
      (T.waldhausen.weq_iso _ inferInstance)
      (T.waldhausen.weq.comp_mem _ _ (b.exact.weak _ (hη X))
        (T.waldhausen.weq_iso _ inferInstance))
  have he : (zeroToMap G).app Y =
      (zeroToMap G).app (a.functor.obj (d.obj Y)) ≫ G.functor.map (ε.hom.app Y) :=
    T.waldhausen.isZero.eq_of_src _ _
  rw [he]
  exact T.waldhausen.weq.comp_mem _ _ (hX (d.obj Y))
    (T.waldhausen.weq_iso _ inferInstance)

/-- The original postwhiskered zero source has its literal chosen-zero transport. -/
theorem zero_postcomp {V W T : Model.{u}} (b : W ⟶ T) :
    zeroHom V T = zeroHom V W ≫ b := by
  simpa only [Category.id_comp] using (zeroHom_square (𝟙 V) b).symm

/-- The original prewhiskered zero source has its literal chosen-zero transport. -/
theorem zero_precomp {V U T : Model.{u}} (a : V ⟶ U) :
    zeroHom V T = a ≫ zeroHom U T := by
  simpa only [Category.comp_id] using zeroHom_square a (𝟙 T)

/-- Postwhisker the specified weak zero transformation, retaining the actual source transport. -/
def postZero {V W T : Model.{u}} {F : V ⟶ W}
    (η : (zeroHom V W).functor ⟶ F.functor) (b : W ⟶ T) :
    (zeroHom V T).functor ⟶ (F ≫ b).functor :=
  eqToHom (congrArg Model.Hom.functor (zero_postcomp b)) ≫ whiskerRight η b.functor

/-- Prewhisker the specified weak zero transformation with its original source transport. -/
def preZero {V U T : Model.{u}} {G : U ⟶ T}
    (θ : (zeroHom U T).functor ⟶ G.functor) (a : V ⟶ U) :
    (zeroHom V T).functor ⟶ (a ≫ G).functor :=
  eqToHom (congrArg Model.Hom.functor (zero_precomp a)) ≫ whiskerLeft a.functor θ

/-- The actual postwhiskered components are weak. -/
theorem postZero_weak {V W T : Model.{u}} {F : V ⟶ W}
    (η : (zeroHom V W).functor ⟶ F.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X)) (b : W ⟶ T) (X : V) :
    T.waldhausen.weq ((postZero η b).app X) :=
  T.waldhausen.weq.comp_mem _ _ (T.waldhausen.weq_iso _ inferInstance)
    (b.exact.weak _ (hη X))

/-- The actual prewhiskered components are weak. -/
theorem preZero_weak {V U T : Model.{u}} {G : U ⟶ T}
    (θ : (zeroHom U T).functor ⟶ G.functor)
    (hθ : ∀ X, T.waldhausen.weq (θ.app X)) (a : V ⟶ U) (X : V) :
    T.waldhausen.weq ((preZero θ a).app X) :=
  T.waldhausen.weq.comp_mem _ _ (T.waldhausen.weq_iso _ inferInstance)
    (hθ (a.functor.obj X))

/-- Zero-source uniqueness gives the actual commuting weak triangle for a specified comparison. -/
theorem triangle_eq {V W U T : Model.{u}} {F : V ⟶ W} {G : U ⟶ T}
    (η : (zeroHom V W).functor ⟶ F.functor)
    (θ : (zeroHom U T).functor ⟶ G.functor) (a : V ⟶ U) (b : W ⟶ T)
    (α : (F ≫ b).functor ≅ (a ≫ G).functor) :
    postZero η b ≫ α.hom = preZero θ a := by
  ext X
  exact T.waldhausen.isZero.eq_of_src _ _

/-- Source transport and postcomposition retain the entire original transformation track. -/
theorem postZero_level {V W T : Model.{u}} {F : V ⟶ W}
    (η : (zeroHom V W).functor ⟶ F.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X)) (b : W ⟶ T) (n : ℕ) :
    (prespectrumTransformationHomotopy (F := zeroHom V T) (G := F ≫ b)
      (postZero η b) (postZero_weak η hη b)).level n =
      ((prespectrumTransformationHomotopy η hη).postcomp (prespectrumMap b)).level n :=
  (prespectrumTransformationHomotopy_source_transport_level
    (F := zeroHom V T) (F' := zeroHom V W ≫ b) (G := F ≫ b) (zero_postcomp b)
    (whiskerRight η b.functor) (fun X ↦ b.exact.weak _ (hη X))
    (postZero_weak η hη b) n).trans
      (prespectrumTransformationHomotopy_postcomp_level (F := zeroHom V W) (G := F) η hη b n)

/-- Source transport and precomposition retain the entire original transformation track. -/
theorem preZero_level {V U T : Model.{u}} {G : U ⟶ T}
    (θ : (zeroHom U T).functor ⟶ G.functor)
    (hθ : ∀ X, T.waldhausen.weq (θ.app X)) (a : V ⟶ U) (n : ℕ) :
    (prespectrumTransformationHomotopy (F := zeroHom V T) (G := a ≫ G)
      (preZero θ a) (preZero_weak θ hθ a)).level n =
      (LoopPrespectrum.Homotopy.precomp (prespectrumMap a)
        (prespectrumTransformationHomotopy θ hθ)).level n :=
  (prespectrumTransformationHomotopy_source_transport_level
    (F := zeroHom V T) (F' := a ≫ zeroHom U T) (G := a ≫ G) (zero_precomp a)
    (whiskerLeft a.functor θ) (fun X ↦ hθ (a.functor.obj X))
    (preZero_weak θ hθ a) n).trans
      (prespectrumTransformationHomotopy_precomp_level (F := zeroHom U T) (G := G) θ hθ a n)

end Quillen.Waldhausen.IteratedS.ModelZeroNormalization
