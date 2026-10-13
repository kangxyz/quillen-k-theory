/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.CategoryTheory.GroupCompletion.ActorChange

/-! # Original representatives and unit arrows under change of actor -/
@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
universe u v w z
namespace Quillen.GroupCompletion.ActionLocalization
variable {C C' : Type u} [Category.{v} C] [Category.{v} C']
  [MonoidalCategory C] [MonoidalCategory C']
  {D E : Type w} [Category.{z} D] [Category.{z} E]
  [MonoidalLeftAction C E] [MonoidalLeftAction C' D]
  (F : C ⥤ C') [F.Monoidal] (G : E ⥤ D)
  (hG : letI := MonoidalLeftAction.restrictAlong (D := D) F; G.LaxLeftLinear C)

example {X Y : E} (f : X ⟶ Y) :
    (mapAlong F G hG).map (ofHom (C := C) f) = ofHom (C := C') (G.map f) :=
  mapAlong_ofHom F G hG f

example {X Y : E} (f : HomRep (C := C) X Y) :
    letI := MonoidalLeftAction.restrictAlong (D := D) F
    letI := hG
    (mapAlong F G hG).map (mkHom f) = mkHom (C := C')
      ⟨F.obj f.denom, Functor.LaxLeftLinear.μₗ G f.denom X ≫ G.map f.map⟩ :=
  mapAlong_mkHom F G hG f

end Quillen.GroupCompletion.ActionLocalization
