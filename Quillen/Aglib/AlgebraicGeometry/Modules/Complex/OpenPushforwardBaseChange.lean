/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pushforward
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.OpenInjectiveModel
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionIsomorphisms

/-! # Original complex direct-image comparisons

Termwise direct image inherits the genuine open base-change isomorphism.
Composition and scheme-isomorphism comparisons retain the original all-sheaf
complexes and maps; no preservation of arbitrary quasi-isomorphisms is claimed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes

/-- Degreewise open base change for the original complexes of all module sheaves. -/
def openPushforwardComplexBaseChangeIso {W U V X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : a ≫ j = b ≫ k)
    (hcart : ∀ v : V, k v ∈ Set.range j → v ∈ Set.range b) :
    pushforwardComplex j ⋙ restrict k ≅ restrict a ⋙ pushforwardComplex b :=
  Functor.mapHomologicalComplexCompIso
    (AlgebraicGeometry.Scheme.Modules.openPushforwardBaseChangeIso a b j k h hcart) _
    ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm

/-- Actual termwise direct image respects composition. -/
def pushforwardComplexCompIso {U V X : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ X) :
    pushforwardComplex a ⋙ pushforwardComplex b ≅ pushforwardComplex (a ≫ b) :=
  Functor.mapHomologicalComplexCompIso (Scheme.Modules.pushforwardComp a b) _

/-- Direct image along a scheme isomorphism is its original inverse restriction. -/
def pushforwardComplexOfIso {U X : Scheme.{u}} (e : U ≅ X) :
    pushforwardComplex e.hom ≅ restrict e.inv :=
  NatIso.mapHomologicalComplex
    (Adjunction.rightAdjointUniq (Scheme.Modules.restrictAdjunction e.hom)
      (moduleRestrictEquivalenceOfIso e).toAdjunction) _

end Quillen.PerfectComplexes
