/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.ExtensionByZero
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.ExtensionByZero

/-! # Genuine open base change for direct image

The original right-adjoint direct-image functors commute with restriction in
a cartesian square of open immersions. The isomorphism follows from the
proved extension-by-zero base change and uniqueness of actual right adjoints.
It imposes no compactness or exactness assumption on ordinary direct image.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Actual direct image and open restriction in a pointwise cartesian open square. -/

def openPushforwardBaseChangeIso {W U V X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : a ≫ j = b ≫ k)
    (hcart : ∀ v : V, k v ∈ Set.range j → v ∈ Set.range b) :
    Scheme.Modules.pushforward j ⋙ Scheme.Modules.restrictFunctor k ≅
      Scheme.Modules.restrictFunctor a ⋙ Scheme.Modules.pushforward b := by
  exact Adjunction.rightAdjointUniq
    ((extensionByZeroRestrictAdjunction k).comp (Scheme.Modules.restrictAdjunction j))
    (((Scheme.Modules.restrictAdjunction b).comp (extensionByZeroRestrictAdjunction a)).ofNatIsoLeft
      (extensionByZeroBaseChangeIso b a k j h.symm (by
        intro u hu
        obtain ⟨v, hv⟩ := hu
        obtain ⟨w, hw⟩ := hcart v (by rw [hv]; exact ⟨u, rfl⟩)
        refine ⟨w, ?_⟩
        apply j.isOpenEmbedding.injective
        have hh := congrArg (fun f : W ⟶ X => f w) h
        simpa only [Scheme.Hom.comp_apply, hw, hv] using hh)))

end AlgebraicGeometry.Scheme.Modules
