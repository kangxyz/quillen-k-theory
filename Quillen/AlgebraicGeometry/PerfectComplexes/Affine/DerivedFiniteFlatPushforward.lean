/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPushforwardComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPerfect
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.Strictification

/-! # Actual bounded-below finite-flat direct image of affine-source perfect objects

Affine strictification gives a global strict model in the original derived category. Full
faithfulness of the bounded-below inclusion lifts that isomorphism, and the original derived unit
identifies its direct image with the established strict finite-flat direct image.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.Affine
/-- The standard ambient derived category used by the original perfect-object predicate. -/
local instance finiteFlatDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- Intrinsic perfectness on an affine scheme supplies an original global strict model in D⁺. -/
theorem exists_strictToDerivedPlus_iso (R : CommRingCat.{u})
    (K : DerivedCategory.Plus (Spec R).Modules)
    (hK : perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj K)) :
    ∃ P : StrictPerfect (Spec R), Nonempty ((strictToDerivedPlus (Spec R)).obj P ≅ K) := by
  obtain ⟨L, ⟨eL⟩⟩ :=
    (perfectDerivedObjects_iff_exists_representative (Spec R) _).mp hK
  obtain ⟨P, ⟨eP⟩⟩ := locallyPerfect_exists_strictPerfect_representative R L.property
  exact ⟨P, ⟨DerivedCategory.Plus.ι.preimageIso (eP ≪≫ eL)⟩⟩

/-- Finite-flat derived direct image preserves intrinsic perfectness for affine source. -/
theorem perfectDerivedObjects_derivedPushforwardPlus {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : Spec R ⟶ X) [IsFinite f] [Flat f] [IsLocallyNoetherian X]
    (K : DerivedCategory.Plus (Spec R).Modules)
    (hK : perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj K)) :
    perfectDerivedObjects X
      (DerivedCategory.Plus.ι.obj ((SchemeSheaf.derivedPushforwardPlus f).obj K)) := by
  obtain ⟨P, ⟨eP⟩⟩ := exists_strictToDerivedPlus_iso R K hK
  let e := (strictFiniteFlatDerivedPushforwardIso f).app P ≪≫
    (SchemeSheaf.derivedPushforwardPlus f).mapIso eP
  apply (perfectDerivedObjects X).prop_of_iso (DerivedCategory.Plus.ι.mapIso e)
  exact (perfectDerivedObjects_toDerived_iff X _).mpr
    (locallyPerfect_of_strictPerfect ((strictFiniteFlatPushforward f).obj P).property)

end Quillen.PerfectComplexes.Affine
