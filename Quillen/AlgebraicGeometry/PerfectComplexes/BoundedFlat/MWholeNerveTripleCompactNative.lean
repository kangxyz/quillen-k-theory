/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskered
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactFamily

/-! Compact evaluation of the four unchanged composition cubes in their shared full reference.
The two outer cubes use `cubeLift_compact_native` with their existing anchors. No new cube,
reference isomorphism, scalar clock, or higher boundary is chosen here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- Compact evaluation preserves every point of any originally reanchored whole cube. -/
theorem cubeLift_compact_native {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
    (F : modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj c))))
    (e : F.functor ≅ (BassOverlap.commonReference P u v).functor)
    (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily F (cubeLift P u v F e) n
      (![r, s, t], x) = (BassMWhole.interiorCube P u v).level n (r, (s, (t, x))) := by
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex F (cubeLift P u v F e)
    (ModelSimplex.reanchorNodes e (BassMWhole.nodes P u v)) ![r, s, t]
    (BassMWhole.scalarCube.{u} ![r, s, t]) rfl n x).trans
      (reanchored_native_cube P u v F e n r s t x)

variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The compact source-whiskered cube keeps the actual coefficient input at every level. -/
theorem precomp_cube_compact_native (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (precompLift P u v w) n
      (![r, s, t], x) = (BassMWhole.interiorCube P v w).level n
        (r, (s, (t, (boundedFlatPerfectPrespectrumMap (coefficientMap P u)).map n x))) := by
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ (precompLift P u v w)
    (precompNodes P u v w) ![r, s, t] (BassMWhole.scalarCube.{u} ![r, s, t]) rfl n x).trans
      (precomp_native_cube P u v w n r s t x)

/-- The compact target-whiskered cube keeps the actual Laurent coefficient output map. -/
theorem postcomp_cube_compact_native (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (postcompLift P u v w) n
      (![r, s, t], x) =
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map w))).map n
        ((BassMWhole.interiorCube P u v).level n (r, (s, (t, x)))) := by
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ (postcompLift P u v w)
    (postcompNodes P u v w) ![r, s, t] (BassMWhole.scalarCube.{u} ![r, s, t]) rfl n x).trans
      (postcomp_native_cube P u v w n r s t x)

end Quillen.PerfectComplexes.BassMWholeNerve
