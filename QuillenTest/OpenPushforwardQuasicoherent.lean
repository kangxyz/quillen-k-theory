/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.OpenPushforwardQuasicoherent

/-!
# Open pushforward and quasicoherent homology

Records the pullback base-change isomorphism and its naturality for complex maps.
The homology statements specialize preservation of quasicoherence to
lower-bounded injective complexes under quasi-compact open pushforward, including
the compact-source corollary and an isomorphic-source comparison.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace QuillenTest.OpenPushforwardQuasicoherent

/-- Actual scheme pullbacks supply the pointwise cartesian condition. -/
def originalPullback {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    pushforwardComplex j ⋙ restrict k ≅
      restrict (pullback.fst j k) ⋙ pushforwardComplex (pullback.snd j k) :=
  openPushforwardComplexBaseChangeIso _ _ j k pullback.condition (by
    intro v hv
    rw [IsOpenImmersion.range_pullbackSnd]
    exact hv)

/-- The actual base-change comparison keeps every original complex morphism. -/
theorem original_map {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] {I J : CochainComplex U.Modules ℤ} (f : I ⟶ J) :
    (restrict k).map ((pushforwardComplex j).map f) ≫ (originalPullback j k).hom.app J =
      (originalPullback j k).hom.app I ≫
        (pushforwardComplex (pullback.snd j k)).map ((restrict (pullback.fst j k)).map f) :=
  (originalPullback j k).hom.naturality f

/-- No ambient compactness, separation or upper cohomological bound is needed. -/
theorem original_homology {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hb : ∀ n, n < a → IsZero (I.X n)) (hi : ∀ n, Injective (I.X n))
    (hq : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    (((pushforwardComplex j).obj I).homology n).IsQuasicoherent :=
  openPushforward_quasicoherent_homology j I a hb hi hq n

/-- The compact-source corollary does not require the ambient scheme compact. -/
theorem compact_source {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [CompactSpace U] [QuasiSeparatedSpace X]
    (I : CochainComplex U.Modules ℤ) (a : ℤ) (hb : ∀ n, n < a → IsZero (I.X n))
    (hi : ∀ n, Injective (I.X n)) (hq : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    (((pushforwardComplex j).obj I).homology n).IsQuasicoherent :=
  compact_openPushforward_quasicoherent_homology j I a hb hi hq n

/-- Isomorphic sources compare through the actual inverse restriction. -/
theorem original_iso {U X : Scheme.{u}} (e : U ≅ X) (I : CochainComplex U.Modules ℤ) :
    (pushforwardComplexOfIso e).hom.app I ≫ (pushforwardComplexOfIso e).inv.app I = 𝟙 _ :=
  (pushforwardComplexOfIso e).hom_inv_id_app I

end QuillenTest.OpenPushforwardQuasicoherent
