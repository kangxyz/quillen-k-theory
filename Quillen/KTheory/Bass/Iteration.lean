/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.KTheory.Bass.Contraction

/-!
Actual functorial iteration of the Bass polynomial/Laurent cokernel. This is a group-level
construction on ring-indexed abelian-group functors.
-/
@[expose] public section


noncomputable section
open CategoryTheory
universe u v
namespace Quillen.Bass

/-- The actual repeated Bass cokernel, functorial in the starting ring-indexed group functor. -/
def iteratedContraction : ℕ →
    (CommRingCat.{u} ⥤ AddCommGrpCat.{v}) ⥤ (CommRingCat.{u} ⥤ AddCommGrpCat.{v})
  | 0 => 𝟭 _
  | n+1 => iteratedContraction n ⋙ contractionFunctor

@[simp] lemma iteratedContraction_zero_obj (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) :
    (iteratedContraction 0).obj F = F := rfl

@[simp] lemma iteratedContraction_succ_obj (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) (n : ℕ) :
    (iteratedContraction (n+1)).obj F = contraction ((iteratedContraction n).obj F) := rfl

@[simp] lemma iteratedContraction_zero_map {F G : CommRingCat.{u} ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) : (iteratedContraction 0).map α = α := rfl

@[simp] lemma iteratedContraction_succ_map {F G : CommRingCat.{u} ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) (n : ℕ) : (iteratedContraction (n+1)).map α =
      contractionMap ((iteratedContraction n).map α) := rfl

/-- The whole original Laurent projection square commutes at every iteration. -/
@[reassoc] lemma iteratedContraction_map_π {F G : CommRingCat.{u} ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) (R : CommRingCat.{u}) (n : ℕ) :
    (contractionπ ((iteratedContraction n).obj F)).app R ≫
      ((iteratedContraction (n+1)).map α).app R =
    ((iteratedContraction n).map α).app (laurentFunctor.obj R) ≫
      (contractionπ ((iteratedContraction n).obj G)).app R :=
  contractionMap_π _ _

end Quillen.Bass

end
