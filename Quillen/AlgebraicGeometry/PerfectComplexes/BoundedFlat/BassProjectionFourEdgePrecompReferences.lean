/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeMap

/-! Full source-domain precomposition of both charts and all four original reference edges. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry Opposite CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Precomp
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
attribute [local irreducible] boundedFlatNormalizedPullback
/-- Source whiskering preserves a chart attachment with its complete composed reference. -/
theorem chart_whiskering {U V W T Z : Model.{u}}
    (A : U ⟶ V) (E : V ⟶ W) (J : W ⟶ T) (K : T ⟶ Z) (F : W ⟶ Z)
    (ε : F.functor ≅ (J ≫ K).functor) (e : CommonReferenceNerve.Node (E ≫ J)) :
    CommonReferenceProduct.postNode ((A ≫ E) ≫ F) K
        (isoWhiskerLeft (A ≫ E).functor ε) (precompNode A e) =
      precompNode A (CommonReferenceProduct.postNode (E ≫ F) K
        (isoWhiskerLeft E.functor ε) e) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp only [CommonReferenceProduct.postNode, CommonReferenceProduct.reanchor,
    precompNode, postcompNode, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {U V : Model.{u + 1}} (A : U ⟶ V)
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => normalizedMap (polynomialProjection P a)

/-- Change only the source model, retaining the entire specified reference isomorphism. -/
def onReference {W : Model.{u + 1}} (F : V ⟶ W) :
    parameterSSet F ⟶ parameterSSet (A ≫ F) :=
  nerveMap (Codiscrete.functorOfFun (precompNode A))

/-- Source whiskering commutes with the complete polynomial attachment node. -/
theorem polynomial_node (e : CommonReferenceNerve.Node E) :
    postcompNode J (precompNode A e) = precompNode A (postcompNode J e) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  rfl

/-- Every one of the original five reference nodes keeps its full anchor under precomposition. -/
theorem reference_node (e : CommonReferenceNerve.Node E) (j : Fin 5) :
    nodes P a (A ≫ E) (precompNode A e) j = precompNode A (nodes P a E e j) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  rfl

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/-- Both charts retain their separate original geometric and normalization isomorphisms. -/
theorem chart_node (e : CommonReferenceNerve.Node (polynomialReference P a E)) :
    chartAttachmentNode P a (A ≫ E) α ha (precompNode A e) =
      precompNode A (chartAttachmentNode P a E α ha e) := by
  exact chart_whiskering A E J (normalizedMap (coefficientMap P (α.app a)))
    (BassProjectionPath.source P a) (BassMJoin.projectionEndpointIso (c := a) P α ha) e

/-- The whole polynomial attachment commutes before realization. -/
theorem attachment :
    FourEdgeTree.attachment E J ≫ onReference A (E ≫ J) =
      onReference A E ≫ FourEdgeTree.attachment (A ≫ E) J := by
  have h : (fun e : CommonReferenceNerve.Node E ↦ precompNode A (postcompNode J e)) =
      (fun e ↦ postcompNode J (precompNode A e)) :=
    funext fun e ↦ (polynomial_node P a A E e).symm
  exact congrArg (fun f ↦ nerveMap (Codiscrete.functorOfFun f)) h

/-- Both entire polynomial chart maps commute with the unchanged source-domain map. -/
theorem chart :
    chartMap P a E α ha ≫ onReference A (reference P a E) =
      onReference A (E ≫ J) ≫ chartMap P a (A ≫ E) α ha := by
  have h :
      (fun e : CommonReferenceNerve.Node (polynomialReference P a E) ↦
        precompNode A (chartAttachmentNode P a E α ha e)) =
      (fun e ↦ chartAttachmentNode P a (A ≫ E) α ha (precompNode A e)) :=
    funext fun e ↦ (chart_node P a A E α ha e).symm
  exact congrArg (fun f ↦ nerveMap (Codiscrete.functorOfFun f)) h

/-- All five whole-nerve vertex maps retain their original full references. -/
theorem vertex (j : Fin 5) :
    vertexMap P a E j ≫ onReference A (reference P a E) =
      onReference A E ≫ vertexMap P a (A ≫ E) j := by
  have h : (fun e : CommonReferenceNerve.Node E ↦ precompNode A (nodes P a E e j)) =
      (fun e ↦ nodes P a (A ≫ E) (precompNode A e) j) :=
    funext fun e ↦ (reference_node P a A E e j).symm
  exact congrArg (fun f ↦ nerveMap (Codiscrete.functorOfFun f)) h

/-- Each complete original cylinder commutes with source precomposition at its unchanged time. -/
theorem edge (i j : Fin 5) :
    edgeMap P a E i j ≫ onReference A (reference P a E) =
      onReference A E ▷ Δ[1] ≫ edgeMap P a (A ≫ E) i j := by
  have h : (fun (e : CommonReferenceNerve.Node E) (k : Fin 2) ↦
        precompNode A (nodes P a E e (![i, j] k))) =
      (fun e k ↦ nodes P a (A ≫ E) (precompNode A e) (![i, j] k)) :=
    funext fun e ↦ funext fun k ↦ (reference_node P a A E e (![i, j] k)).symm
  exact congrArg (FiniteParameter.simplicial E (reference P a (A ≫ E))) h

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Precomp
