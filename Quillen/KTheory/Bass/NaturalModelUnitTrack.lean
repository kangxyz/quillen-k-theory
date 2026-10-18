/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.NaturalTrack
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIsoNaturality
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismSquare
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismEvaluation

/-! # Realization of original identity units as whole natural tracks -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u v w
namespace Quillen.KTheory.Bass.NaturalTrack
variable {C : Type u} [Category.{v} C] (L : C ⥤ C) (c : 𝟭 C ⟶ L)
    (F : C ⥤ Model.{w})
    (unit : ∀ X, 𝟭 (F.obj (L.obj X)) ≅ 𝟭 (F.obj (L.obj X)))
    (hunit : ∀ {X Y} (g : X ⟶ Y),
      Preserves (F.map (L.map g)).functor (unit X) (unit Y))

/-- The original identity-unit realization, along the prescribed coefficient projection. -/
def ofModelUnits : Track L c (F ⋙ prespectrumFunctor) where
  homotopy X := prespectrumIsoHomotopy (F.map (c.app X))
    (onFunctor (F.map (c.app X)).functor (unit X))
  naturality {X Y} g n r x := by
    have h : F.map (c.app X) ≫ F.map (L.map g) = F.map g ≫ F.map (c.app Y) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg F.map (c.naturality g).symm
    exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
      (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg Model.Hom.functor h))
        (unit X) (unit Y) (hunit g).whisker) n r x

/-- A unit-preserving actual Model transformation retains the entire realization time. -/
theorem ofModelUnits_equivariant (G : C ⥤ Model.{w})
    (unit' : ∀ X, 𝟭 (G.obj (L.obj X)) ≅ 𝟭 (G.obj (L.obj X)))
    (hunit' : ∀ {X Y} (g : X ⟶ Y),
      Preserves (G.map (L.map g)).functor (unit' X) (unit' Y))
    (η : F ⟶ G)
    (hη : ∀ X, Preserves (η.app (L.obj X)).functor (unit X) (unit' X)) :
    Equivariant (ofModelUnits L c F unit hunit)
      (ofModelUnits L c G unit' hunit') (Functor.whiskerRight η prespectrumFunctor) := by
  intro X r
  exact (prespectrumIsoHomotopy_square_at _ _ _ _ _ _ (η.naturality (c.app X))
    (onFunctor_whisker_square _ _ _ _
      (eqToHom (congrArg Model.Hom.functor (η.naturality (c.app X))))
      (unit X) (unit' X) (hη X).whisker) r).symm

end Quillen.KTheory.Bass.NaturalTrack
