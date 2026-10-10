/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Models
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenDerivedRoofs

/-! # Actual derived roofs for arbitrary globally perfect models

The genuine finite-projective module roof and original affine strictification
are combined using globally weak common right denominators. Both final chain
numerators land in the unchanged original all-sheaf complexes.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard

/-- Every original derived arrow between restricted global perfect complexes
has a genuine globally perfect locally weak roof on a compact affine open. -/
theorem affine_hasDerivedRoofs (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) : HasDerivedRoofs W.ι := by
  let Q : ObjectProperty (Complex (Spec R)) := fun A =>
    ∃ P : Affine.ModuleComplex R, Affine.moduleStrictPerfect R P ∧ A = (Affine.associatedComplex
      R).obj P
  apply hasDerivedRoofs_of_models W.ι Q
  · intro A hA
    obtain ⟨P, hP, eP⟩ := Affine.locallyPerfect_exists_moduleStrictPerfect_representative R hA
    exact ⟨(Affine.associatedComplex R).obj P, ⟨P, hP, rfl⟩, eP⟩
  · rintro _ _ ⟨A, hA, rfl⟩ ⟨P, hP, rfl⟩ α
    obtain ⟨B, hB, q, a, hq, ha⟩ :=
      Affine.exists_quasiCompact_open_strict_module_roof R W hW hA hP α
    exact ⟨(Affine.associatedComplex R).obj B, (Affine.associatedComplex R).map q,
      (Affine.associatedComplex R).map a,
      locallyPerfect_of_strictPerfect (Affine.strictPerfect_associated R hB), hq, ha⟩

end Quillen.PerfectComplexes.OpenDerivedImage
