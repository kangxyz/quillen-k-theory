/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.ClassifyingSpace.Opposite
public import Quillen.Topology.ClassifyingSpace.Constant

/-! The natural opposite-realization homeomorphism preserves each object
vertex, as follows immediately by naturality for the constant endofunctor. -/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
universe u
namespace Quillen
variable {C : Type u} [SmallCategory C]

private theorem point_of_const_square {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : TopCat.const x ≫ f = f ≫ TopCat.const y) : f x = y :=
  ConcreteCategory.congr_hom h x

@[simp] theorem classifyingOppositeIso_point (c : C) :
    (classifyingOppositeIso C).hom (classifyingSpacePoint (op c)) = classifyingSpacePoint c := by
  let F : C ⥤ C := (Functor.const C).obj c
  have hf : F.op = (Functor.const Cᵒᵖ).obj (op c) := rfl
  have h₁ : classifyingSpaceMap F.op =
      TopCat.const (X := ClassifyingSpace Cᵒᵖ) (classifyingSpacePoint (op c)) :=
    (congrArg classifyingSpaceMap hf).trans (classifyingSpaceMap_const_direct (op c))
  have h₂ : classifyingSpaceMap F =
      TopCat.const (X := ClassifyingSpace C) (classifyingSpacePoint c) :=
    classifyingSpaceMap_const_direct c
  have h := classifyingOppositeIso_naturality F
  have hc : TopCat.const (classifyingSpacePoint (op c)) ≫ (classifyingOppositeIso C).hom =
      (classifyingOppositeIso C).hom ≫ TopCat.const (classifyingSpacePoint c) :=
    (congrArg (fun k ↦ k ≫ (classifyingOppositeIso C).hom) h₁.symm).trans
      (h.trans (congrArg (fun k ↦ (classifyingOppositeIso C).hom ≫ k) h₂))
  exact point_of_const_square (classifyingOppositeIso C).hom _ _ hc


end Quillen
