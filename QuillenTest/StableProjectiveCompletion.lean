/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.StableProjectiveCompletion
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of the original right-telescope completion square

The successor formula, all original matrix arrows, the prescribed zero-stage
unit entry, and the stable zero-component map are checked without an IBN or
nontriviality assumption, including explicit specialization to the zero ring.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory
open Quillen Quillen.FiniteProjectiveModule
open Quillen.FiniteProjectiveModule.StableFreeRight
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric

namespace QuillenTest.StableProjectiveCompletion
variable (R : Type u) [Ring R]

/-- The generic cocone extension retains the actual prescribed projective successor. -/
theorem original_successor (n : ℕ) {P Q : IsoCategory Rᵐᵒᵖ}
    (f : (tensorRight (freeIso Rᵐᵒᵖ 1)).obj P ⟶ Q) :
    (originalCompletionFunctor R).map
      (EndofunctorTelescope.successorArrow (tensorRight (freeIso Rᵐᵒᵖ 1)) n f) =
      (completionStep R n).app P ≫ (completionFiber R (n + 1)).map f :=
  EndofunctorTelescope.functorFromSequence_map_successor _
    (completionFiber R) (completionStep R) n f

/-- Every original matrix telescope arrow is preserved in the strict completion square. -/
theorem original_matrix_arrow
    {X Y : StableGeneralLinear.GrothendieckModel.Telescope R} (f : X ⟶ Y) :
    (completionFunctor R).map ((telescopeFunctor R).map f) =
      (StableCompletion.telescopeFunctor R).map f := by
  have h := Functor.congr_hom (telescopeFunctor_completionFunctor R) f
  simpa only [Functor.comp_obj, Functor.comp_map, eqToHom_refl,
    Category.id_comp, Category.comp_id] using h

/-- At zero, the exact old unit-entry functor is recovered. -/
theorem original_unit_entry :
    Grothendieck.ι (projectiveTelescopeDiagram R) 0 ⋙ completionFunctor R =
      AsSmall.down ⋙ GroupCompletion.Localization.unitEntry
        (C := IsoCategory Rᵐᵒᵖ) (D := IsoCategory Rᵐᵒᵖ) :=
  completionFunctor_zero_inclusion R

/-- This exact matrix square is valid over the zero ring. -/
theorem zero_ring_original_square :
    telescopeFunctor (ZMod 1) ⋙ completionFunctor (ZMod 1) =
      StableCompletion.telescopeFunctor (ZMod 1) :=
  telescopeFunctor_completionFunctor (ZMod 1)

/-- The zero-ring stable map also retains its actual zero-component value. -/
theorem zero_ring_original_stable_map
    (x : ClassifyingSpace (SingleObj (StableGeneralLinear.Group (ZMod 1)))) :
    classifyingSpaceMapUniversal (completionFunctor (ZMod 1))
      (classifyingSpaceMapUniversal (telescopeFunctor (ZMod 1))
        (StableCompletion.originalStableToTelescope (ZMod 1) x)) =
      (StableCompletion.stableZeroMap (ZMod 1) x).val :=
  stableZeroMap_completionMap_val (ZMod 1) x

end QuillenTest.StableProjectiveCompletion
