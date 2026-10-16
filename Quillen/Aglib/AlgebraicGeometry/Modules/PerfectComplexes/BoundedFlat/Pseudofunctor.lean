/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.UnitCoherence
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! The original bounded-flat pullback categories with their proved geometric pseudofunctor laws. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Bicategory
universe u
namespace Quillen.PerfectComplexes

/-- The actual bounded-flat geometric pseudofunctor, before any strictification or normalization. -/
def boundedFlatPerfectPseudofunctor : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun X => ↧(BoundedFlatPerfect X.unop))
    (fun f => (boundedFlatPerfectPullback f.unop).toCatHom)
    (fun X => Cat.Hom.isoMk (boundedFlatPerfectPullbackIdIso X.unop))
    (fun f g => Cat.Hom.isoMk (boundedFlatPerfectPullbackCompIso g.unop f.unop)) ?_ ?_ ?_
  · intro W X Y Z f g h
    ext1
    exact boundedFlatPerfectPullbackCompIso_associativity h.unop g.unop f.unop
  · intro X Y f
    ext1
    exact boundedFlatPerfectPullbackCompIso_left_unitality f.unop
  · intro X Y f
    ext1
    exact boundedFlatPerfectPullbackCompIso_right_unitality f.unop

/-- Affine coefficient change uses the original `Spec` functor and actual geometric pullbacks. -/
def boundedFlatAffinePseudofunctor : Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat :=
  Scheme.Spec.rightOp.toPseudofunctor.comp boundedFlatPerfectPseudofunctor

/-- The affine pseudofunctor retains the original bounded-flat category. -/
theorem boundedFlatAffinePseudofunctor_obj (R : CommRingCat.{u}) :
    boundedFlatAffinePseudofunctor.obj ⟨R⟩ = ↧(BoundedFlatPerfect (Spec R)) := rfl

/-- Every coefficient arrow is the actual original bounded-flat pullback functor. -/
theorem boundedFlatAffinePseudofunctor_map {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffinePseudofunctor.map f.toLoc).toFunctor =
      boundedFlatPerfectPullback (Spec.map f) := rfl

end Quillen.PerfectComplexes
