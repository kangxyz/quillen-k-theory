/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TwoOpenFirstCohomology

/-! Consumers of the original connecting map: an overlap section has zero
obstruction exactly when it is an actual chart coboundary, and every first
cohomology class comes from an overlap section on a two-affine cover. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.TwoOpen
universe u
namespace QuillenTest.TwoOpenFirstCohomology

open Quillen

lemma firstConnecting_zero_iff {X : Scheme.{u}} (M : X.Modules) (I : InjectiveResolution M)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (z : Γ(M, U ⊓ V)) :
    (firstConnecting M I U V hUV).hom z = 0 ↔
      ∃ a : Γ(M, U), ∃ b : Γ(M, V), difference M U V (a, b) = z := by
  constructor
  · intro hz
    obtain ⟨⟨a, b⟩, hab⟩ := (ShortComplex.ab_exact_iff _).mp
      (firstCohomologySequence_exact M I U V hUV) z hz
    exact ⟨a, b, hab⟩
  · rintro ⟨a, b, rfl⟩
    have h := congrArg (fun f => AddCommGrpCat.Hom.hom f (a, b))
      (difference_firstConnecting M I U V hUV)
    exact h

lemma first_class_has_overlap_representative {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (I : InjectiveResolution M) {R S : CommRingCat.{u}}
    (j : Spec R ⟶ X) (k : Spec S ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : j.opensRange ⊔ k.opensRange = ⊤)
    (w : ((sectionsFunctor X ⊤).rightDerived 1).obj M) :
    ∃ z : Γ(M, j.opensRange ⊓ k.opensRange),
      (firstConnecting M I j.opensRange k.opensRange hcover).hom z = w :=
  (AddCommGrpCat.epi_iff_surjective _).mp
    (firstConnecting_epi_of_affine_cover M I j k hcover) w

end QuillenTest.TwoOpenFirstCohomology
