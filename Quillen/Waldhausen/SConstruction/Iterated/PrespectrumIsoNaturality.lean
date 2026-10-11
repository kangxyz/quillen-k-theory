/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopyNaturality

/-!
# Literal naturality of original model automorphism homotopies

An automorphism of an actual zero-preserving exact model morphism gives its original whole
prespectrum self-homotopy. A strictly commuting model square with the actual transformation
square preserves that entire homotopy, including the degree-zero loop and structure parameters.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.Waldhausen.IteratedS

/-- The original transformation homotopy of an automorphism of an exact model morphism. -/
def prespectrumIsoHomotopy {V W : Model.{u}} (F : V ⟶ W) (e : F.functor ≅ F.functor) :
    LoopPrespectrum.Homotopy (prespectrumMap F) (prespectrumMap F) :=
  prespectrumTransformationHomotopy e.hom (fun _ ↦ W.waldhausen.weq_iso _ inferInstance)

/-- Equality transport of a model morphism retains the entire supplied automorphism track. -/
theorem prespectrumIsoHomotopy_congr_level {V W : Model.{u}} {F G : V ⟶ W}
    (h : F = G) (e : F.functor ≅ F.functor) (e' : G.functor ≅ G.functor)
    (he : e.hom ≫ eqToHom (congrArg Model.Hom.functor h) =
      eqToHom (congrArg Model.Hom.functor h) ≫ e'.hom) (n : ℕ) :
    (prespectrumIsoHomotopy F e).level n = (prespectrumIsoHomotopy G e').level n := by
  subst G
  have he' : e.hom = e'.hom := by simpa using he
  have he'' : e = e' := Iso.ext he'
  subst e'
  rfl

/-- A strict model square and its original automorphism square preserve every interval value. -/
theorem prespectrumIsoHomotopy_square_apply {V W T U : Model.{u}}
    (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (e : F.functor ≅ F.functor) (e' : G.functor ≅ G.functor) (h : F ≫ b = a ≫ G)
    (he : Functor.whiskerRight e.hom b.functor ≫
        eqToHom (congrArg Model.Hom.functor h) =
      eqToHom (congrArg Model.Hom.functor h) ≫ Functor.whiskerLeft a.functor e'.hom)
    (n : ℕ) (t : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumMap b).map n ((prespectrumIsoHomotopy F e).level n (t, x)) =
      (prespectrumIsoHomotopy G e').level n (t, (prespectrumMap a).map n x) := by
  have hp := prespectrumTransformationHomotopy_postcomp_level e.hom
    (fun _ ↦ W.waldhausen.weq_iso _ inferInstance) b n
  have hq := prespectrumTransformationHomotopy_precomp_level e'.hom
    (fun _ ↦ U.waldhausen.weq_iso _ inferInstance) a n
  have hc := prespectrumIsoHomotopy_congr_level h
    (Functor.isoWhiskerRight e b.functor) (Functor.isoWhiskerLeft a.functor e') he n
  exact (congrArg (fun k ↦ k (t, x)) hp).symm.trans
    ((congrArg (fun k ↦ k (t, x)) hc).trans (congrArg (fun k ↦ k (t, x)) hq))

/-- Every time slice is strictly natural on the original whole prespectrum maps. -/
theorem prespectrumIsoHomotopy_square_at {V W T U : Model.{u}}
    (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (e : F.functor ≅ F.functor) (e' : G.functor ≅ G.functor) (h : F ≫ b = a ≫ G)
    (he : Functor.whiskerRight e.hom b.functor ≫
        eqToHom (congrArg Model.Hom.functor h) =
      eqToHom (congrArg Model.Hom.functor h) ≫ Functor.whiskerLeft a.functor e'.hom)
    (t : unitInterval) :
    (prespectrumIsoHomotopy F e).at t ≫ prespectrumMap b =
      prespectrumMap a ≫ (prespectrumIsoHomotopy G e').at t := by
  apply LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact prespectrumIsoHomotopy_square_apply F G a b e e' h he n t x

end Quillen.Waldhausen.IteratedS
