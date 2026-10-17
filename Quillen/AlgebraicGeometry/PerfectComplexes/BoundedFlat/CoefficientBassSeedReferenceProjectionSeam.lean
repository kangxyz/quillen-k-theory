/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionWholeReferenceAttachments

/-! Full chart-reference transport along the actual source polynomial projection. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedReferenceProjectionSeam
open BassH0Merge CommonReferenceNerve BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a c : Under R)
variable (E : modelOf (boundedFlatPerfectWaldhausen
  (space (op P, (polynomialUnderFunctor R).obj a))) ⟶
  modelOf (boundedFlatPerfectWaldhausen (space (op P, c))))
local notation "A" => normalizedMap (polynomialProjection P a)

/-- Source projection preserves the complete ordinary positive chart attachment node. -/
theorem positive_chart_node
    (m : Node (polynomialReference P c E)) :
    chartAttachmentNode P c (A ≫ E) (underToLaurent R) (laurentPlus_projection P c)
        (precompNode A m) =
      precompNode A
        (chartAttachmentNode P c E (underToLaurent R) (laurentPlus_projection P c) m) := by
  apply Sigma.ext (Model.Hom.ext rfl)
  apply heq_of_eq
  apply Iso.ext
  rfl

/-- The entire polynomial-source reference nerve obeys the same actual projection seam. -/
theorem positive_chart_parameter
    (x : |nerve (Codiscrete (Node (polynomialReference P c E)))|) :
    mapParameter
        (chartAttachmentNode P c (A ≫ E) (underToLaurent R) (laurentPlus_projection P c))
        (mapParameter (precompNode A) x) =
      mapParameter (precompNode A)
        (mapParameter
          (chartAttachmentNode P c E (underToLaurent R) (laurentPlus_projection P c)) x) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter (polynomialReference P c E) x
  have leftInner := mapParameter_parameter (precompNode A) N z
  have leftOuter := mapParameter_parameter
    (chartAttachmentNode P c (A ≫ E) (underToLaurent R) (laurentPlus_projection P c))
    (fun i ↦ precompNode A (N i)) z
  have rightInner := mapParameter_parameter
    (chartAttachmentNode P c E (underToLaurent R) (laurentPlus_projection P c)) N z
  have rightOuter := mapParameter_parameter (precompNode A)
    (fun i ↦ chartAttachmentNode P c E (underToLaurent R)
      (laurentPlus_projection P c) (N i)) z
  exact (congrArg
    (mapParameter (chartAttachmentNode P c (A ≫ E)
      (underToLaurent R) (laurentPlus_projection P c))) leftInner).trans
    (leftOuter.trans ((congrArg (fun M ↦ parameter (reference P c (A ≫ E)) M z)
      (funext fun i ↦ positive_chart_node P a c E (N i))).trans
        ((congrArg (mapParameter (precompNode A)) rightInner).trans rightOuter).symm))

end Quillen.PerfectComplexes.CoefficientBassSeedReferenceProjectionSeam
