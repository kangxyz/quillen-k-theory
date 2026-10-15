/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.StrictPerfectKEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.PullbackIso

/-! # Presentation-independent original K equivalences for affine schemes

The original comparison on an arbitrary affine scheme is transported through
its actual canonical spectrum isomorphism and original pullback naturality.
No affine presentation or replacement comparison is supplied as a hypothesis.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
/-- Any affine scheme has the genuine original strict/perfect comparison,
without choosing or supplying a presentation by a spectrum. -/
lemma strictToPerfectKMap_bijective_of_isAffine (X : Scheme.{u}) [IsAffine X] (n : ℕ) :
    Function.Bijective (strictToPerfectKMap X n) := by
  have h := (perfectKPullback_iso_bijective X.isoSpec n).comp
    (Affine.strictToPerfectKMap_bijective Γ(X, ⊤) n)
  change Function.Bijective ((perfectKPullback X.isoSpec.hom n).comp
    (strictToPerfectKMap _ n)) at h
  rw [strictToPerfectKMap_pullback] at h
  exact (Function.Bijective.of_comp_iff _ (strictKPullback_iso_bijective X.isoSpec n)).mp h

/-- The original vector-bundle comparison is bijective on every affine scheme. -/
lemma vectorBundleToPerfectKMap_bijective_of_isAffine (X : Scheme.{u}) [IsAffine X] (n : ℕ) :
    Function.Bijective (vectorBundleToPerfectKMap X n) := by
  rw [← strictToPerfect_comp_vectorBundleToStrictKMap]
  exact (strictToPerfectKMap_bijective_of_isAffine X n).comp (vectorBundleToStrictKMap_bijective
    X n)

/-- Original strict/perfect K equivalence without an affine presentation choice. -/
def affineStrictToPerfectKEquiv (X : Scheme.{u}) [IsAffine X] (n : ℕ) :
    StrictK X n ≃* PerfectK X n :=
  MulEquiv.ofBijective (strictToPerfectKMap X n) (strictToPerfectKMap_bijective_of_isAffine X n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] lemma affineStrictToPerfectKEquiv_coe (X : Scheme.{u}) [IsAffine X] (n : ℕ) :
    ↑(affineStrictToPerfectKEquiv X n) = strictToPerfectKMap X n := rfl

/-- Original vector-bundle/perfect K equivalence on every affine scheme. -/
def affineVectorBundleToPerfectKEquiv (X : Scheme.{u}) [IsAffine X] (n : ℕ) :
    AlgebraicGeometry.Scheme.K X n ≃* PerfectK X n :=
  MulEquiv.ofBijective (vectorBundleToPerfectKMap X n)
    (vectorBundleToPerfectKMap_bijective_of_isAffine X n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] lemma affineVectorBundleToPerfectKEquiv_coe (X : Scheme.{u}) [IsAffine X] (n : ℕ) :
    ↑(affineVectorBundleToPerfectKEquiv X n) = vectorBundleToPerfectKMap X n := rfl

/-- The actual strict inverse is natural for every morphism of affine schemes. -/
lemma affineStrictToPerfectKEquiv_symm_pullback {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (n : ℕ) (x : PerfectK Y n) :
    (affineStrictToPerfectKEquiv X n).symm (perfectKPullback f n x) =
      strictKPullback f n ((affineStrictToPerfectKEquiv Y n).symm x) := by
  apply (strictToPerfectKMap_bijective_of_isAffine X n).injective
  change affineStrictToPerfectKEquiv X n ((affineStrictToPerfectKEquiv X n).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (strictToPerfectKMap_pullback f n)
    ((affineStrictToPerfectKEquiv Y n).symm x)
  exact h.symm.trans (congrArg (perfectKPullback f n)
    ((affineStrictToPerfectKEquiv Y n).apply_symm_apply x)) |>.symm

/-- The actual vector-bundle inverse is natural for every affine scheme morphism. -/
lemma affineVectorBundleToPerfectKEquiv_symm_pullback {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (n : ℕ) (x : PerfectK Y n) :
    (affineVectorBundleToPerfectKEquiv X n).symm (perfectKPullback f n x) =
      AlgebraicGeometry.Scheme.pullbackK f n ((affineVectorBundleToPerfectKEquiv Y n).symm x) := by
  apply (vectorBundleToPerfectKMap_bijective_of_isAffine X n).injective
  change affineVectorBundleToPerfectKEquiv X n ((affineVectorBundleToPerfectKEquiv X n).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (vectorBundleToPerfectKMap_pullback f n)
    ((affineVectorBundleToPerfectKEquiv Y n).symm x)
  exact h.symm.trans (congrArg (perfectKPullback f n)
    ((affineVectorBundleToPerfectKEquiv Y n).apply_symm_apply x)) |>.symm
end Quillen.PerfectComplexes
