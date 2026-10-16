/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Aglib.AlgebraicGeometry.Modules.Flat.Closure

/-!
# Retracts of stalkwise-flat module sheaves

Actual module stalks send sheaf retracts to module retracts. Flatness therefore
passes to retracts, and the full category of stalkwise-flat module sheaves is
idempotent complete. No quasicoherence or affineness is required.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

instance stalkwiseFlat_isStableUnderRetracts (X : Scheme.{u}) :
    (stalkwiseFlat X).IsStableUnderRetracts where
  of_retract h hN := stalkwiseFlat_of_retract h hN

/-- Idempotents in the actual flat sheaf subcategory split through actual flat sheaves. -/

instance stalkwiseFlat_isIdempotentComplete (X : Scheme.{u}) :
    IsIdempotentComplete (stalkwiseFlat X).FullSubcategory where
  idempotents_split M p hp := by
    obtain ⟨N, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split M.obj p.hom
      (congrArg (fun f : M ⟶ M => f.hom) hp)
    have hN : stalkwiseFlat X N := stalkwiseFlat_of_retract ⟨i, r, hir⟩ M.property
    refine ⟨⟨N, hN⟩, (stalkwiseFlat X).homMk i, (stalkwiseFlat X).homMk r, ?_, ?_⟩
    · exact ObjectProperty.hom_ext _ hir
    · exact ObjectProperty.hom_ext _ hri

end AlgebraicGeometry.Scheme.Modules
