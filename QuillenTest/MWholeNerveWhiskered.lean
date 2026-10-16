/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskered

/-! Named clients retain both original whiskered cubes at level zero and preserve the original
based point and an independently varying structure time throughout the unchanged scalar cube. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace QuillenTest.MWholeNerveWhiskered
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Source whiskering retains the original level-zero input and unchanged complete cube. -/
theorem original_precomp_level_zero (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    CommonReferenceNerve.prespectrumFamily _ (BassMWholeNerve.precompNodes P u v w) 0
        (BassMWhole.scalarCube.{u} ![r, s, t], x) =
      (BassMWhole.interiorCube P v w).level 0
        (r, (s, (t, (boundedFlatPerfectPrespectrumMap (coefficientMap P u)).map 0 x))) :=
  BassMWholeNerve.precomp_native_cube P u v w 0 r s t x

/-- Target whiskering retains the actual Laurent coefficient map at original level zero. -/
theorem original_postcomp_level_zero (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    CommonReferenceNerve.prespectrumFamily _ (BassMWholeNerve.postcompNodes P u v w) 0
        (BassMWhole.scalarCube.{u} ![r, s, t], x) =
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map w))).map 0
        ((BassMWhole.interiorCube P u v).level 0 (r, (s, (t, x)))) :=
  BassMWholeNerve.postcomp_native_cube P u v w 0 r s t x

/-- The original based point is fixed on the entire source-whiskered parameter cube. -/
theorem original_precomp_point (n : ℕ) (r s t : unitInterval) :
    CommonReferenceNerve.prespectrumFamily _ (BassMWholeNerve.precompNodes P u v w) n
        (BassMWhole.scalarCube.{u} ![r, s, t],
          (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))).point n :=
  CommonReferenceNerve.prespectrumFamily_point _ _ n _

/-- Structure time remains independent from all three original target-whiskered cube times. -/
theorem original_postcomp_structure (n : ℕ) (r s t q : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.prespectrumFamily _ (BassMWholeNerve.postcompNodes P u v w) (n + 1)
        (BassMWhole.scalarCube.{u} ![r, s, t],
          (originalPrespectrum (boundedFlatPerfectWaldhausen
            (space (op P, a)))).structureMap n x q) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))).structureMap n
          (CommonReferenceNerve.prespectrumFamily _ (BassMWholeNerve.postcompNodes P u v w) n
            (BassMWhole.scalarCube.{u} ![r, s, t], x)) q :=
  CommonReferenceNerve.prespectrumFamily_structure _ _ n _ x q

end QuillenTest.MWholeNerveWhiskered
