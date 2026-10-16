/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.GlobalUnitPullback
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Units

/-! Actual scalar and geometric-comparison consumers under arbitrary Laurent coefficient change. -/
@[expose] public section

open CommRingCat.PolynomialLaurent
open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.LaurentUnitPullback

open Quillen
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Every actual Laurent module sheaf has the unchanged pulled-back coordinate action. -/
theorem sheaf_scalar (M : (Spec (.of (LaurentPolynomial R))).Modules) :
    (Scheme.Modules.pullback (Spec.map (laurentMap f))).map
      ((AlgebraicGeometry.Scheme.Modules.globalScalar _ (↑(laurentGlobalUnit R))).app M) =
    (AlgebraicGeometry.Scheme.Modules.globalScalar _ (↑(laurentGlobalUnit S))).app
      ((Scheme.Modules.pullback (Spec.map (laurentMap f))).obj M) := by
  have h := congrArg Units.val (laurentGlobalUnit_coefficient f)
  change (Spec.map (laurentMap f)).appTop (↑(laurentGlobalUnit R)) =
    ↑(laurentGlobalUnit S) at h
  rw [AlgebraicGeometry.Scheme.Modules.pullback_map_globalScalar, h]

/-- The original bounded-flat coefficient pullback preserves the actual Laurent automorphism. -/
theorem original_unit (K : BoundedFlatPerfect (Spec (.of (LaurentPolynomial R)))) :
    (boundedFlatPerfectPullback (Spec.map (laurentMap f))).map
      ((boundedFlatPerfectGlobalUnitIso _ (laurentGlobalUnit R)).hom.app K) =
    (boundedFlatPerfectGlobalUnitIso _ (laurentGlobalUnit S)).hom.app
      ((boundedFlatPerfectPullback (Spec.map (laurentMap f))).obj K) := by
  rw [boundedFlatPerfectPullback_map_globalUnit, laurentGlobalUnit_coefficient]

/-- The genuine Laurent projection comparison retains its unit square under coefficient change. -/
theorem original_projection_comparison :
    (boundedFlatPerfectPullbackCompIso (Spec.map (laurentMap f)) (laurentProjection R)).hom ≫
      Functor.whiskerRight
        (boundedFlatPerfectPullbackUnitIso (laurentProjection R) (laurentGlobalUnit R)).hom
        (boundedFlatPerfectPullback (Spec.map (laurentMap f))) =
    (boundedFlatPerfectPullbackUnitIso (Spec.map (laurentMap f) ≫ laurentProjection R)
      (laurentGlobalUnit S)).hom ≫
        (boundedFlatPerfectPullbackCompIso (Spec.map (laurentMap f))
          (laurentProjection R)).hom := by
  simpa only [laurentGlobalUnit_coefficient] using
    boundedFlatPerfectPullbackUnitIso_comp (Spec.map (laurentMap f)) (laurentProjection R)
      (laurentGlobalUnit R)

end QuillenTest.LaurentUnitPullback
