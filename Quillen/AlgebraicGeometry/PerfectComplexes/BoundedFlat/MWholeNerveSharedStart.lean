/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveHZero

/-!
# The shared entire starting face of the two fixed outer composition cubes

The original cubes for `(u ≫ v, w)` and `(u, v ≫ w)` lift to a single actual common-reference
nerve. Their complete initial faces agree after the displayed geometric associativity transport.
The chosen whole cubes remain unchanged. Whiskered cubes, other shared faces, correction prisms
and the higher relative filler are not constructed here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- Transport of the actual H0 characteristic map along equality of its coefficient arrow. -/
theorem h0_parameter_transport {a d : Under R} {f g : a ⟶ d} (h : f = g)
    (s t : unitInterval) :
    CommonReferenceNerve.parameter (BassH0Diagram.reference P f)
        (ModelSimplex.reanchorNodes
          (eqToIso (congrArg (fun k ↦ (BassH0Diagram.reference P k).functor) h))
          (BassH0Diagram.nodes P g)) (BassH0Diagram.parameter (s, t)) =
      CommonReferenceNerve.parameter (BassH0Diagram.reference P f)
        (BassH0Diagram.nodes P f) (BassH0Diagram.parameter (s, t)) := by
  subst g
  simp only [eqToIso_refl, reanchor_nodes_refl]

variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The second fixed cube uses precisely associativity and its original inverse H0 anchor. -/
def rightStartingAnchor : (BassH0Diagram.reference P ((u ≫ v) ≫ w)).functor ≅
    (BassOverlap.commonReference P u (v ≫ w)).functor :=
  eqToIso (congrArg (fun k ↦ (BassH0Diagram.reference P k).functor) (Category.assoc u v w)) ≪≫
    h0Anchor P u (v ≫ w)

/-- The two unchanged outer composition cubes agree on their entire starting nerve face. -/
theorem fixed_outer_cubes_shared_start (s t : unitInterval) :
    cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (h0Anchor P (u ≫ v) w) ![0, s, t] =
      cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w) ![0, s, t] := by
  calc
    _ = CommonReferenceNerve.parameter (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (BassH0Diagram.nodes P ((u ≫ v) ≫ w)) (BassH0Diagram.parameter (s, t)) :=
      cubeLift_original_h0 P (u ≫ v) w s t
    _ = CommonReferenceNerve.parameter (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (ModelSimplex.reanchorNodes
          (eqToIso (congrArg (fun k ↦ (BassH0Diagram.reference P k).functor)
            (Category.assoc u v w))) (BassH0Diagram.nodes P (u ≫ v ≫ w)))
        (BassH0Diagram.parameter (s, t)) :=
      (h0_parameter_transport P (Category.assoc u v w) s t).symm
    _ = _ := by
      rw [cubeLift_zero]
      simp only [rightStartingAnchor, h0Anchor, Iso.trans_assoc, Iso.symm_self_id,
        Iso.trans_refl]

end Quillen.PerfectComplexes.BassMWholeNerve
