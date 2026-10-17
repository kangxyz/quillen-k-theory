/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionWholeReference

/-!
# Actual polynomial-source factorization of both overlap attachments

The polynomial attachment is defined on its entire reference nerve. Its composite with the
original coefficient-to-polynomial node map is the complete original chart endpoint.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference
open BassH0Merge CommonReferenceNerve
attribute [local irreducible] boundedFlatNormalizedPullback
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))

/-- The polynomial reference has the literal original projection as its second factor. -/
abbrev polynomialReference := E ≫ normalizedMap (polynomialProjection P a)

/-- The actual coefficient-to-polynomial map retains every original full reference. -/
def polynomialNode (e : CommonReferenceNerve.Node E) :
    CommonReferenceNerve.Node (polynomialReference P a E) :=
  postcompNode (normalizedMap (polynomialProjection P a)) e

/-- Each Laurent chart attachment is defined on arbitrary polynomial-reference nodes. -/
def chartAttachmentNode (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (m : CommonReferenceNerve.Node (polynomialReference P a E)) :
    CommonReferenceNerve.Node (reference P a E) :=
  CommonReferenceProduct.postNode (reference P a E)
    (normalizedMap (coefficientMap P (α.app a)))
    (isoWhiskerLeft E.functor (BassMJoin.projectionEndpointIso (c := a) P α ha)) m

/-- The two postcompositions give the original chart endpoint with its entire reference. -/
theorem chartAttachmentNode_polynomialNode
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (e : CommonReferenceNerve.Node E) :
    chartAttachmentNode P a E α ha (polynomialNode P a E e) = chartNode P a E α ha e := by
  apply Sigma.ext (Model.Hom.ext rfl)
  apply heq_of_eq
  rfl

/-- The whole endpoint map factors through the actual polynomial-source reference nerve. -/
theorem chartAttachment_parameter_polynomial
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (x : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) :
    mapParameter (chartAttachmentNode P a E α ha)
      (mapParameter (polynomialNode P a E) x) = mapParameter (chartNode P a E α ha) x := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter E x
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun M ↦ CommonReferenceNerve.parameter (reference P a E) M z)
  funext i
  exact chartAttachmentNode_polynomialNode P a E α ha (N i)

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference
