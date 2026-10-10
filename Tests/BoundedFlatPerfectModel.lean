/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Functor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Cylinder

/-! # Consumers of the actual bounded-flat Waldhausen enhancement

These use genuine ambient cofibrations, original complex maps, arbitrary
scheme pullback, all connective degrees and the actual structural cylinder.
No equivalence with the original Perf model is assumed.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.SchemeSheaf
universe u
namespace Quillen.Tests.BoundedFlatPerfectModel

/-- The model functor retains the literal original chain map. -/
theorem original_chain_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : BoundedFlatPerfect Y} (s : K ⟶ L) :
    ((boundedFlatPerfectPullback f).map s).hom = (pullbackComplex f).map s.hom := rfl

/-- Arbitrary geometric pullback preserves genuine quotient cofibrations. -/
theorem original_cofibration {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : BoundedFlatPerfect Y} (s : K ⟶ L)
    (hs : (boundedFlatPerfectWaldhausen Y).cof s) :
    (boundedFlatPerfectWaldhausen X).cof ((boundedFlatPerfectPullback f).map s) :=
  (boundedFlatPerfectPullback_exact f).cofibration s hs

/-- Quasi-isomorphisms of the actual complexes remain quasi-isomorphisms. -/
theorem original_quasiIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : BoundedFlatPerfect Y} (s : K ⟶ L) [QuasiIso s.hom] :
    QuasiIso ((boundedFlatPerfectPullback f).map s).hom :=
  (boundedFlatPerfectPullback_exact f).weak s (inferInstanceAs (QuasiIso s.hom))

/-- Pullback keeps the specified termwise upper bound, not only some later bound. -/
theorem same_upper_bound {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : BoundedFlatPerfect Y) (b : ℤ) [K.obj.IsStrictlyLE b] :
    ((boundedFlatPerfectPullback f).obj K).obj.IsStrictlyLE b := by
  apply (CochainComplex.isStrictlyLE_iff _ _).mpr
  intro n hn
  exact (Scheme.Modules.pullback f).map_isZero (K.obj.isZero_of_isStrictlyLE b n hn)

/-- The genuine cylinder is available without an input JointData premise. -/
def actual_joint_data (X : Scheme.{u}) :
    Quillen.Waldhausen.Fibration.RowFactorization.JointData
      (Quillen.Waldhausen.Fibration.NestedWeakEquivalences.refl
        (boundedFlatPerfectWaldhausen X)) := boundedFlatPerfectJointData X

/-- Every degree has a strictly functorial K-map on arbitrary scheme morphisms. -/
theorem original_K_composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    boundedFlatPerfectKPullback (f ≫ g) n =
      (boundedFlatPerfectKPullback f n).comp (boundedFlatPerfectKPullback g n) :=
  boundedFlatPerfectKPullback_comp f g n

/-- The actual strict comparison is natural even in degree zero. -/
theorem strict_zero_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatPerfectKPullback f 0).comp (strictToBoundedFlatPerfectKMap Y 0) =
      (strictToBoundedFlatPerfectKMap X 0).comp (strictKPullback f 0) :=
  strictToBoundedFlatPerfectKMap_pullback f 0

/-- The chain of original inclusions recovers the original strict-to-perfect map. -/
theorem original_comparison_factorization (X : Scheme.{u}) (n : ℕ) :
    (boundedFlatPerfectToPerfectKMap X n).comp (strictToBoundedFlatPerfectKMap X n) =
      strictToPerfectKMap X n := boundedFlatPerfectToPerfect_comp_strict X n

/-- Compatibility with the original Perf map is stated under its actual flat hypothesis. -/
theorem original_Perf_flat_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ) :
    (perfectKFlatPullback f n).comp (boundedFlatPerfectToPerfectKMap Y n) =
      (boundedFlatPerfectToPerfectKMap X n).comp (boundedFlatPerfectKPullback f n) :=
  boundedFlatPerfectToPerfectKMap_flatPullback f n

end Quillen.Tests.BoundedFlatPerfectModel
