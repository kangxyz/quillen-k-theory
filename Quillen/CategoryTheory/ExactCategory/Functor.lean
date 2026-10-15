/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.CategoryTheory.ExactCategory.Basic
public import Quillen.CategoryTheory.QConstruction.Functor

/-!
# Exact functors and Q-functoriality

The general exact functor and its pullback preservation are supplied by Aglib.
This module retains the Q-construction application.
-/
@[expose] public section

noncomputable section
universe v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits

namespace Quillen
export CategoryTheory.ExactCategory (ExactFunctor pullbackMatrixKernel)
end Quillen

namespace CategoryTheory.ExactCategory.ExactFunctor
open Quillen

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

/-- Every exact functor satisfies the Q-compatibility conditions. The selective
pullback-preservation field is a theorem of exactness, not extra supplied data. -/
def toQCompatibleFunctor :
    QCompatibleFunctor E.deflation E.inflation E'.deflation E'.inflation where
  toFunctor := F.toFunctor
  map_deflation := F.map_deflation
  map_inflation := F.map_inflation
  preserves_mixed i p _hi hp := F.preserves_pullback i p hp

/-- The Q-functor genuinely induced by an additive conflation-preserving functor. -/
def mapQ : Q E.deflation E.inflation ⥤ Q E'.deflation E'.inflation :=
  F.toQCompatibleFunctor.mapQ

@[simp]
theorem mapQ_obj_of (X : C) :
    F.mapQ.obj (Q.of E.deflation E.inflation X) =
      Q.of E'.deflation E'.inflation (F.toFunctor.obj X) := rfl

@[simp]
theorem mapQ_mkHom {X Y : C} (s : Span E.deflation E.inflation X Y) :
    F.mapQ.map (Q.mkHom E.deflation E.inflation s) =
      Q.mkHom E'.deflation E'.inflation (F.toQCompatibleFunctor.mapSpan s) := rfl

/-- Exact-functor identities induce identity Q-functors. -/
@[simp]
theorem mapQ_id (E : ExactStructure C) : (id E).mapQ = 𝟭 (Q E.deflation E.inflation) := by
  refine Functor.hext ?_ ?_
  · intro X
    rfl
  · rintro X Y ⟨s⟩
    rfl

/-- Exact-functor composition is respected by the Q-construction. -/
@[simp]
theorem mapQ_comp {T : Type u₃} [Category.{v₃} T] [Preadditive T] [HasFiniteBiproducts T]
    {E'' : ExactStructure T} (G : ExactFunctor E' E'') :
    (F.comp G).mapQ = F.mapQ ⋙ G.mapQ := by
  refine Functor.hext ?_ ?_
  · intro X
    rfl
  · rintro X Y ⟨s⟩
    rfl

end CategoryTheory.ExactCategory.ExactFunctor
