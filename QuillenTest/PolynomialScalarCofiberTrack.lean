/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberFiberTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone

/-! # Original signed polynomial cofiber transport in the canonical fiber -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
open AlgebraicGeometry.Scheme.PolynomialLaurent Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Topology
universe u
namespace QuillenTest.PolynomialScalarCofiberTrack

open Quillen
variable (R : CommRingCat.{u}) (K : Perfect (Spec (.of (Polynomial R))))

/-- The initial face is the unchanged original universal cofiber's canonical fiber loop. -/
theorem original_cofiber_face (t : unitInterval) :
    perfectOpenScalarCofiberFiberTrack (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (0, t) =
      canonicalFiberObjectLoop (perfectOpenNested (laurentPlus R))
        (perfectOpenScalarCofiberAcyclic (laurentPlus R) (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K) t :=
  (perfectOpenScalarCofiberFiberTrack (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K).apply_zero t

/-- The final face is the already existing polynomial scalar cone fiber loop. -/
theorem original_cone_face (t : unitInterval) :
    perfectOpenScalarCofiberFiberTrack (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (1, t) =
      polynomialScalarConeFiberLoop R K t :=
  (perfectOpenScalarCofiberFiberTrack (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K).apply_one t

/-- All three independent times survive the original canonical fiber's null path. -/
theorem original_three_parameters (a t s : unitInterval) :
    (perfectOpenScalarCofiberFiberTrack (laurentPlus R) (polynomialGlobalCoordinate R)
      (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (a, t)).val.2 s =
      acyclicNullhomotopy (perfectOpenNested (laurentPlus R))
        (s, (acyclicStructure (perfectOpenNested (laurentPlus R))).weakObjectLoopTrack
          (perfectOpenScalarCofiberAcyclicIso (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K).hom
          ((acyclicStructure (perfectOpenNested (laurentPlus R))).weq_iso _ inferInstance)
          (a, t)) :=
  perfectOpenScalarCofiberFiberTrack_path (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K a t s

/-- On the final face the fiber-path time is precisely the reversed original zero-track time. -/
theorem original_reversed_final_path (t s : unitInterval) :
    (perfectOpenScalarCofiberFiberTrack (laurentPlus R) (polynomialGlobalCoordinate R)
      (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (1, t)).val.2 s =
      acyclicObjectTransformationTrack (perfectOpenNested (laurentPlus R))
        (polynomialScalarCone R K) (unitInterval.symm s, t) := by
  rw [original_cone_face]
  exact canonicalFiberObjectLoop_path_transformation _ _ t s

end QuillenTest.PolynomialScalarCofiberTrack
