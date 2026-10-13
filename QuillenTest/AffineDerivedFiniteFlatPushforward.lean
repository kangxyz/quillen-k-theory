/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedFiniteFlatPushforward
public import Mathlib.Data.ZMod.Basic

/-! Original derived perfectness and the concrete strict-model direct-image isomorphism. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine Quillen.SchemeSheaf
universe u
namespace QuillenTest.AffineDerivedFiniteFlatPushforward

open Quillen
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

lemma original_strict_image_model {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : Spec R ⟶ X) [IsFinite f] [Flat f] [IsLocallyNoetherian X]
    (K : DerivedCategory.Plus (Spec R).Modules)
    (hK : perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj K)) :
    ∃ (P : StrictPerfect (Spec R)) (e : (strictToDerivedPlus (Spec R)).obj P ≅ K),
      IsIso ((derivedPushforwardPlusUnit f).app ((strictToPlus (Spec R)).obj P) ≫
        (derivedPushforwardPlus f).map e.hom) := by
  obtain ⟨P, ⟨e⟩⟩ := exists_strictToDerivedPlus_iso R K hK
  refine ⟨P, e, ?_⟩
  let := isIso_derivedPushforwardPlusUnit_strict f P
  infer_instance

lemma original_derived_output_perfect {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : Spec R ⟶ X) [IsFinite f] [Flat f] [IsLocallyNoetherian X]
    (K : DerivedCategory.Plus (Spec R).Modules)
    (hK : perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj K)) :
    ∃ P : Perfect X, Nonempty ((toDerived X).obj P.obj ≅
      DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus f).obj K)) :=
  (perfectDerivedObjects_iff_exists_representative X _).mp
    (perfectDerivedObjects_derivedPushforwardPlus f K hK)

lemma nonreduced_identity (K : DerivedCategory.Plus (Spec (.of (ZMod 4))).Modules)
    (hK : perfectDerivedObjects (Spec (.of (ZMod 4))) (DerivedCategory.Plus.ι.obj K)) :
    perfectDerivedObjects (Spec (.of (ZMod 4))) (DerivedCategory.Plus.ι.obj
      ((derivedPushforwardPlus (𝟙 (Spec (.of (ZMod 4))))).obj K)) :=
  perfectDerivedObjects_derivedPushforwardPlus _ K hK

end QuillenTest.AffineDerivedFiniteFlatPushforward
