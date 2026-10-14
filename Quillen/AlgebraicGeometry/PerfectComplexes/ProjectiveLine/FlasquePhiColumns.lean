/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueGPhiMatrix
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlasqueShift
public import Quillen.Waldhausen.Additivity.GroupFormula

/-!
# Actual Phi columns and the signed PhiG formula

The literal two-summand coproduct and its actual totalization give the two
column K-maps. The actual signed base shift converts G1 into the inverse of
the unshifted coefficient map. These formulas do not assert PhiG is the identity.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiColumns
open FlasqueTwoSummands FlasqueCoefficients

def positive (R : CommRingCat.{u}) := first R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

lemma positive_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof (FlasqueBoundedBelow.waldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (positive R) :=
  (first_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

def negative (R : CommRingCat.{u}) := second R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

lemma negative_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof (FlasqueBoundedBelow.waldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (negative R) :=
  (second_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

def unshiftedCoefficient (R : CommRingCat.{u}) := rightTensorTotal R ⋙ G0 R

lemma unshiftedCoefficient_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof (FlasqueBoundedBelow.waldhausen (Spec R)).weq
    (unshiftedCoefficient R) := (rightTensorTotal_exact R).comp (G0_exact R)

lemma G1_KMap_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n) :
    Waldhausen.KMap (G1_exact R) n x =
      (Waldhausen.KMap (unshiftedCoefficient_exact R) n x)⁻¹ := by
  have h := DFunLike.congr_fun (Waldhausen.KMap_comp_KMap
    (unshiftedCoefficient_exact R) (modelShift_exact (Spec R) 1) n) x
  exact h.symm.trans (FlasqueBoundedBelow.KMap_modelShift_one_apply _ n _)

lemma Phi_KMap_sum_apply (R : CommRingCat.{u}) (n : ℕ)
    (z : (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).K n) :
    Waldhausen.KMap (Phi_exact R) n z =
      Waldhausen.KMap (positive_exact R) n
        (Waldhausen.KMap (Waldhausen.ExtensionCategory.fst_exact
          (FlasqueBoundedBelow.waldhausen (Spec R))
          (FlasqueBoundedBelow.waldhausen (Spec R))) n z) *
      Waldhausen.KMap (negative_exact R) n
        (Waldhausen.KMap (Waldhausen.ExtensionCategory.snd_exact
          (FlasqueBoundedBelow.waldhausen (Spec R))
          (FlasqueBoundedBelow.waldhausen (Spec R))) n z) := by
  let W := FlasqueBoundedBelow.waldhausen (Spec R)
  have hsum := Waldhausen.Additivity.KMap_sum_apply
    (Waldhausen.ExtensionCategory.productStructure W W)
    (BoundedBelow.waldhausen (twoChartLine R))
    ((Waldhausen.ExtensionCategory.fst_exact W W).comp (first_exact R))
    ((Waldhausen.ExtensionCategory.snd_exact W W).comp (second_exact R)) n z
  have ht := DFunLike.congr_fun (Waldhausen.KMap_comp_KMap
    (beforeTotal_exact R) (FlasqueBoundedBelow.total_exact (twoChartLine R)) n) z
  simp only [MonoidHom.comp_apply] at ht
  rw [← ht, hsum, map_mul]
  rw [← Waldhausen.KMap_comp_KMap (Waldhausen.ExtensionCategory.fst_exact W W)
    (first_exact R) n, ← Waldhausen.KMap_comp_KMap
      (Waldhausen.ExtensionCategory.snd_exact W W) (second_exact R) n]
  simp only [MonoidHom.comp_apply]
  exact congrArg₂ (fun a b => a * b)
    (DFunLike.congr_fun (Waldhausen.KMap_comp_KMap (first_exact R)
      (FlasqueBoundedBelow.total_exact (twoChartLine R)) n)
      (Waldhausen.KMap (Waldhausen.ExtensionCategory.fst_exact W W) n z))
    (DFunLike.congr_fun (Waldhausen.KMap_comp_KMap (second_exact R)
      (FlasqueBoundedBelow.total_exact (twoChartLine R)) n)
      (Waldhausen.KMap (Waldhausen.ExtensionCategory.snd_exact W W) n z))

/-- The original composite is its actual positive column times the inverse negative column. -/
theorem Phi_comp_G_KMap_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n) :
    Waldhausen.KMap (Phi_exact R) n (Waldhausen.KMap (G_exact R) n x) =
      Waldhausen.KMap ((G0_exact R).comp (positive_exact R)) n x *
        (Waldhausen.KMap ((unshiftedCoefficient_exact R).comp (negative_exact R)) n x)⁻¹ := by
  have h := Phi_KMap_sum_apply R n (Waldhausen.KMap (G_exact R) n x)
  have hg := FlasquePhiEntries.G_KEquiv_apply R n x
  have hg0 := congrArg _root_.Prod.fst hg
  have hg1 := congrArg _root_.Prod.snd hg
  change Waldhausen.KMap (Waldhausen.ExtensionCategory.fst_exact
    (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))) n
    (Waldhausen.KMap (G_exact R) n x) = _ at hg0
  change Waldhausen.KMap (Waldhausen.ExtensionCategory.snd_exact
    (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))) n
    (Waldhausen.KMap (G_exact R) n x) = _ at hg1
  rw [hg0, hg1, G1_KMap_apply, map_inv] at h
  rw [← Waldhausen.KMap_comp_KMap (G0_exact R) (positive_exact R) n,
    ← Waldhausen.KMap_comp_KMap (unshiftedCoefficient_exact R) (negative_exact R) n]
  exact h

end Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiColumns
