/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.Factorization


public import Quillen.AlgebraicGeometry.PerfectComplexes.KTheory
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.DerivedRoofs
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.KernelClosure
public import Quillen.Aglib.Algebra.Homology.HomotopyPullback.QuasiIso
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.HomotopyPullback
public import Quillen.Waldhausen.WeakArrow.Structure

/-!
# Actual affine weak-arrow target dual factorization

For the original strict-to-perfect inclusion over any commutative ring,
every map into a target of an actual weak-arrow object factors through a
weak map and an original weak-arrow morphism. Both components of that
morphism are split epic in every degree, with actual strict-perfect and
locally-perfect kernels. All factorization and comma-square equations are
literal equalities of chain maps.

Two genuine mapping-cocone homotopy pullbacks rectify the original derived
roof. This supplies the geometric dual approximation input of
Thomason–Trobaugh, Theorem 1.9.8. The independent functorial cocylinder and
dual K-comparison steps are not assumed or inferred here.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.CochainComplex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- Literal dual factorization for the target of the original strict-to-perfect
weak-arrow category, with actual componentwise split epis and kernel facts. -/
lemma weakArrow_target_dual_factorization (R : CommRingCat.{u})
    (X : Waldhausen.WeakArrow.Obj (perfectWaldhausen (Spec R)) (strictToPerfect (Spec R)))
    (B' : Perfect (Spec R))
    (b : B' ⟶ (Waldhausen.WeakArrow.target (perfectWaldhausen (Spec R))
      (strictToPerfect (Spec R))).obj X) :
    ∃ (Y : Waldhausen.WeakArrow.Obj (perfectWaldhausen (Spec R)) (strictToPerfect (Spec R)))
      (f : Y ⟶ X)
      (v : B' ⟶ (Waldhausen.WeakArrow.target (perfectWaldhausen (Spec R))
        (strictToPerfect (Spec R))).obj Y),
      (perfectWaldhausen (Spec R)).weq v ∧
      v ≫ (Waldhausen.WeakArrow.target (perfectWaldhausen (Spec R))
        (strictToPerfect (Spec R))).map f = b ∧
      (∀ i, IsSplitEpi (f.hom.left.hom.f i)) ∧
      (∀ i, IsSplitEpi (f.hom.right.hom.f i)) ∧
      strictPerfect (Spec R) (kernel f.hom.left.hom) ∧
      locallyPerfect (Spec R) (kernel f.hom.right.hom) := by
  have hw : QuasiIso X.obj.hom.hom := X.property
  obtain ⟨C, D, c, d, u, v, hD, hu, hv, hsq, he, hc, hd, hkc, hkd⟩ :=
    exists_strict_dual_factorization R X.obj.left X.obj.right.obj B'.obj B'.property
      X.obj.hom.hom b.hom
  let Y : Waldhausen.WeakArrow.Obj (perfectWaldhausen (Spec R)) (strictToPerfect (Spec R)) :=
    ⟨⟨C, ⟨D, hD⟩, ObjectProperty.homMk u⟩, hu⟩
  let f : Y ⟶ X := ObjectProperty.homMk
    ⟨ObjectProperty.homMk c, ObjectProperty.homMk d, ObjectProperty.hom_ext _ hsq.symm⟩
  exact ⟨Y, f, ObjectProperty.homMk v, hv, ObjectProperty.hom_ext _ he,
    hc, hd, hkc, hkd⟩

end Quillen.PerfectComplexes.Affine
