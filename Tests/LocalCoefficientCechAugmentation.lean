/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.CechTotalQuasiIso
public import Quillen.Topology.LocalCoefficients.CechIntersections

/-! Regression tests for the original twisted Čech total augmentation and spatial maps. -/

@[expose] public section

noncomputable section

open CategoryTheory Quillen.LocalCoefficients
open scoped Simplicial

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {ι κ : Type u}

example (U : ι → Set X) (A : System.{u, u} X) :
    QuasiIso (cechSmallChainAugmentation U A) :=
  cechSmallChainAugmentation_quasiIso U A

example (U : ι → Set X) (A : System.{u, u} X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    QuasiIso (cechSingularAugmentation U A) :=
  cechSingularAugmentation_quasiIso U A hU hcover

example (U : ι → Set X) (A : System.{u, u} X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cechSingularAugmentation U A) n) :=
  cechSingularAugmentation_homology_isIso U A hU hcover n

example (f : C(X, Y)) (U : ι → Set X) (V : κ → Set Y) (index : ι → κ)
    (h : ∀ i, Set.MapsTo f (U i) (V (index i))) (A : System.{u, u} Y) :
    cechPushforwardTotal f U V index h A ≫ cechTotalAugmentation V A =
      cechTotalAugmentation U (pullback f A) ≫
        HomologicalComplex₂.total.map (smallSinglePushforwardBicomplex f U V index h A)
          (ComplexShape.down ℕ) :=
  cechPushforwardTotal_augmentation f U V index h A

example (U : ι → Set X) (A : System.{u, u} X) (p : SimplexCategory) :
    cechSingularColumnComplex U A p ≅ cechIntersectionColumnComplex U A p :=
  cechIntersectionColumnIso U A p
