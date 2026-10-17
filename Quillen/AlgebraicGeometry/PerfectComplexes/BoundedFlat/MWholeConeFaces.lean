/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeReference

/-! The six unchanged full-reference faces of the frozen M cube. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier
open CommonReferenceNerve BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The whole original 140-node family, with its full reference transported once. -/
def parameter : C(StdSimplex ℝ (Fin 140),
    |nerve (Codiscrete (CommonReferenceNerve.Node
      (reference P c (inputReference P p q))))|) :=
  (mapParameter (CommonReferenceProduct.reanchor (referenceIso P p q))).comp
    (CommonReferenceNerve.parameter (BassOverlap.commonReference P p q) (BassMWhole.nodes P p q))

theorem laurentCube_zero (s t : I) :
    laurentCube P p q (0, (s, t)) = parameter P p q (BassMWhole.h0Parameter (s, t)) := by
  dsimp only [laurentCube, parameter, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [BassMWhole.cube_zero]

theorem laurentCube_one (s t : I) :
    laurentCube P p q (1, (s, t)) = parameter P p q (BassMWhole.h1Parameter.{u} (s, t)) := by
  dsimp only [laurentCube, parameter, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [BassMWhole.cube_one]

theorem laurentCube_bottom (r t : I) :
    laurentCube P p q (r, (0, t)) = parameter P p q (BassMWhole.bottomParameter.{u} (r, t)) := by
  dsimp only [laurentCube, parameter, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [BassMWhole.cube_bottom]

theorem laurentCube_top (r t : I) :
    laurentCube P p q (r, (1, t)) = parameter P p q (BassMWhole.mParameter.{u} (r, t)) := by
  dsimp only [laurentCube, parameter, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [BassMWhole.cube_top]

theorem laurentCube_left (r s : I) :
    laurentCube P p q (r, (s, 0)) = parameter P p q (BassMWhole.plusParameter (r, s)) := by
  dsimp only [laurentCube, parameter, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [BassMWhole.cube_left]

theorem laurentCube_right (r s : I) :
    laurentCube P p q (r, (s, 1)) = parameter P p q (BassMWhole.minusParameter (r, s)) := by
  dsimp only [laurentCube, parameter, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [BassMWhole.cube_right]

end Quillen.PerfectComplexes.BassMWholeConeCarrier
