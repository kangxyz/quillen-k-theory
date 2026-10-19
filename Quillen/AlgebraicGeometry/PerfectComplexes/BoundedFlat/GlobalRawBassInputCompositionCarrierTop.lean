/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTopAssoc

/-!
# The whole original global input-composition M carrier face

The complete original vertex stage is followed by the reverse of the prescribed five-piece
reassociation. Every native point is the existing span-composition homotopy after the unchanged
Bass comparison. Both clocks, the based points and independent prespectrum structure time
are retained. This face does not supply the remaining comparison-cube edges or a cube.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells Quillen.ScalarRectangle
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionCarrierTop
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The entire prescribed M surface retains both of its original composition-time halves. -/
def face : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  concatFirst (InputCompositionTopVertex.face f g)
    (InputCompositionTopWord.reverseReassociation f g)
    (fun t ↦ (InputCompositionTopWord.reverse_zero f g t).symm)

/-- The original first composition half is the whole unchanged vertex surface. -/
theorem face_lower (r t : unitInterval) :
    face f g (lower r, t) = InputCompositionTopVertex.face f g (r, t) :=
  concatFirst_lower _ _ _ r t

/-- The second original composition half is the complete reverse reassociation. -/
theorem face_upper (r t : unitInterval) :
    face f g (upper r, t) = InputCompositionTopWord.reassociation f g
      (unitInterval.symm r, t) :=
  concatFirst_upper _ _ _ r t

/-- Every actual M carrier value has its original native span-composition value. -/
theorem face_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (face f g) n ((r, t), x) =
      (InputCompositionCharts.spanTrack f g).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x)) := by
  refine (CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (InputCompositionCarrierCharts.source f g) (face f g) n (r, t) x).symm.trans ?_
  rcases cover r with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [face_lower]
    exact (CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
      (InputCompositionCarrierCharts.source f g) (InputCompositionTopVertex.face f g)
      n (s, t) x).trans (InputCompositionTopVertex.face_native f g n s t x)
  · rw [face_upper]
    refine (InputCompositionTopAssoc.reassociation_native f g n x (unitInterval.symm s) t).trans ?_
    exact (congrArg ((comparison X).map n)
      (InputCompositionSpan.homotopy_cylinder_upper f g n s t x)).symm

/-- The entire M face keeps its original based point at both independent coordinates. -/
theorem face_point (n : ℕ) (r t : unitInterval) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (face f g) n ((r, t), (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).point n) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X))).point n :=
  CommonReferenceNerve.compactPrespectrumFamily_point _ _ n (r, t)

/-- Both original M coordinates remain independent of the native prespectrum structure time. -/
theorem face_structure (n : ℕ) (r t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (face f g) (n + 1)
        ((r, t), (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).structureMap n x z) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X))).structureMap n
        (CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
          (face f g) n ((r, t), x)) z :=
  CommonReferenceNerve.compactPrespectrumFamily_structure _ _ n (r, t) x z

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionCarrierTop
