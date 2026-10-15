/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPushforwardComparison

/-! Consumers retain the actual bounded derived unit and strict finite-flat naturality square. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules Quillen.PerfectComplexes
universe u
namespace QuillenTest.DerivedPushforwardComparison

open Quillen
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

lemma bounded_original_unit_cancel {Z X : Scheme.{u}} (f : Z ⟶ X) [IsAffineHom f]
    (K : CochainComplex.Plus Z.Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i))
    (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hqc : ∀ i, (K.obj.X i).IsQuasicoherent)
    {T : DerivedCategory.Plus X.Modules}
    (p q : T ⟶ ((Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q).obj K) :
    p ≫ (derivedPushforwardPlusUnit f).app K = q ≫ (derivedPushforwardPlusUnit f).app K ↔
      p = q := by
  let := isIso_derivedPushforwardPlusUnit_of_term_bounds f K a b hl hu hqc
  exact cancel_mono _

lemma original_comparison_inverse {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsFinite f] [Flat f] [IsLocallyNoetherian X] (K : StrictPerfect Z) :
    (derivedPushforwardPlusUnit f).app ((strictToPlus Z).obj K) ≫
      (strictFiniteFlatDerivedPushforwardIso f).inv.app K = 𝟙 _ :=
  (strictFiniteFlatDerivedPushforwardIso f).hom_inv_id_app K

lemma original_strict_naturality {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsFinite f] [Flat f] [IsLocallyNoetherian X]
    {K L : StrictPerfect Z} (g : K ⟶ L) :
    (strictToDerivedPlus X).map ((strictFiniteFlatPushforward f).map g) ≫
        (derivedPushforwardPlusUnit f).app ((strictToPlus Z).obj L) =
      (derivedPushforwardPlusUnit f).app ((strictToPlus Z).obj K) ≫
        (derivedPushforwardPlus f).map ((strictToDerivedPlus Z).map g) :=
  (strictFiniteFlatDerivedPushforwardIso f).hom.naturality g

lemma original_strict_unit_identity (X : Scheme.{u}) (K : StrictPerfect X) :
    IsIso ((derivedPushforwardPlusUnit (𝟙 X)).app ((strictToPlus X).obj K)) :=
  isIso_derivedPushforwardPlusUnit_strict (𝟙 X) K

end QuillenTest.DerivedPushforwardComparison
