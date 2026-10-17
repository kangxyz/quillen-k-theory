/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0C0SeedAlignment

/-!
# Both actual C0 source projection rails

The complete three-node row is the last positive rectangle rail. Its two edges retain their
original binary clock; the plus sheet keeps the specified common-unit reference action.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0C0ProjectionSeam
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierRails

/-- The literal right binary row, before embedding into the common full-node simplex. -/
def rightFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨BassH0Merge.rightIndex, by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [BassH0Merge.rightIndex]⟩

/-- The full reference-preserving positive projection row. -/
def projectionFace : ⦋2⦌ ⟶ ⦋30⦌ :=
  rightFace ≫ DoubleSquareMergedSimplex.lastFace ≫ BassH0Diagram.plusFace

/-- The embedded binary parameter is exactly the original new-positive rail. -/
theorem projectionFace_parameter (s : I) :
    StdSimplex.map projectionFace.toOrderHom (binaryPath (k := 2) 0 1 2 s) =
      ProjectionRectangleParameters.K BassH0Diagram.plusFace s := by
  exact map_binaryPath projectionFace 0 1 2 s

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- All barycentric values agree because the full dependent node row is identical. -/
theorem sourceProjection_newPositive (s : I) :
    sourceProjectionParameter P p q s =
      parameter (laurentReference P p q) (BassH0Merge.nodes P p q)
        (ProjectionRectangleParameters.K BassH0Diagram.plusFace s) := by
  rw [← projectionFace_parameter, parameter_face]; rfl

variable (d : Under R)

/-- The ordinary C0 source projection is the entire actual J0 new-positive path. -/
theorem projectionMinus_newPositive (s : I) :
    CoefficientBassPositiveJ0C0SeedAlignment.toJ0 P d
      (CoefficientBassPositiveC0CarrierSeed.projectionMinus P
        ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) (s, 0)) =
      CoefficientBassPositiveJ0Rectangles.newPositiveMinus P d s := by
  rw [CoefficientBassPositiveC0CarrierSeed.source_projection]
  change CoefficientBassPositiveC0CarrierSeed.includeLaurent P
    ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) _ =
    CoefficientBassPositiveC0CarrierSeed.includeLaurent P
      ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) _
  exact congrArg _ (sourceProjection_newPositive P
    ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) s)

/-- The shifted C0 source projection retains the whole common-unit action on the same row. -/
theorem projectionPlus_newPositive (s : I) :
    CoefficientBassPositiveJ0C0SeedAlignment.toJ0 P d
      (CoefficientBassPositiveC0CarrierSeed.projectionPlus P
        ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) (s, 0)) =
      CoefficientBassPositiveJ0Rectangles.newPositivePlus P d s := by
  rw [CoefficientBassPositiveC0CarrierSeed.source_projection_shifted]
  change CoefficientBassPositiveC0CarrierSeed.includeLaurent P
    ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)
      (mapParameter _ _) =
    CoefficientBassPositiveC0CarrierSeed.includeLaurent P
      ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)
        (mapParameter _ _)
  exact congrArg _ (congrArg _ (sourceProjection_newPositive P
    ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) s))

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0C0ProjectionSeam
