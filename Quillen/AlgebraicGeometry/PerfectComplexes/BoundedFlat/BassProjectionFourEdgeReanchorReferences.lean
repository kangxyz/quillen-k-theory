/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeMap

/-! Exact input-reference changes on the original polynomial charts and four overlap edges. -/
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
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Reanchor
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CommonReferenceProduct
attribute [local irreducible] boundedFlatNormalizedPullback

/-- Source-reference change commutes with an entire polynomial node. -/
theorem post_whiskering {V W T : Model.{u}} {E E' : V ⟶ W}
    (δ : E'.functor ≅ E.functor) (J : W ⟶ T) (e : CommonReferenceNerve.Node E) :
    postcompNode J (reanchor δ e) =
      reanchor (isoWhiskerRight δ (J).functor) (postcompNode J e) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  exact (J).functor.map_comp _ _

/-- Naturality of the fixed chart anchor controls its full input-reference change. -/
theorem chart_whiskering {V W T Z : Model.{u}} {E E' : V ⟶ W}
    (δ : E'.functor ≅ E.functor) (J : W ⟶ T) (K : T ⟶ Z) (F : W ⟶ Z)
    (ε : (F).functor ≅ (J ≫ K).functor) (e : CommonReferenceNerve.Node (E ≫ J)) :
    postNode (E' ≫ F) K (isoWhiskerLeft E'.functor ε)
        (reanchor (F₀ := E' ≫ J) (F₁ := E ≫ J) (isoWhiskerRight δ (J).functor) e) =
      reanchor (isoWhiskerRight δ (F).functor)
        (postNode (E ≫ F) K (isoWhiskerLeft E.functor ε) e) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  change ε.hom.app (E'.functor.obj X) ≫
      K.functor.map ((J).functor.map (δ.hom.app X) ≫ e.2.hom.app X) =
    (F).functor.map (δ.hom.app X) ≫ ε.hom.app (E.functor.obj X) ≫
      K.functor.map (e.2.hom.app X)
  have h := ε.hom.naturality (δ.hom.app X)
  change (F).functor.map (δ.hom.app X) ≫ ε.hom.app (E.functor.obj X) =
    ε.hom.app (E'.functor.obj X) ≫ K.functor.map ((J).functor.map (δ.hom.app X)) at h
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ f ≫ K.functor.map (e.2.hom.app X)) h.symm

/-- Both factors retain the original composition-functor reference under reanchoring. -/
theorem pair_whiskering {V W T : Model.{u}} {E E' : V ⟶ W} (F : W ⟶ T)
    (δ : E'.functor ≅ E.functor) (e : CommonReferenceNerve.Node E)
    (m : CommonReferenceNerve.Node F) :
    (⟨e.1 ≫ m.1, (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso
      ((δ ≪≫ e.2).prod m.2)⟩ : CommonReferenceNerve.Node (E' ≫ F)) =
    reanchor (isoWhiskerRight δ (F).functor)
      (⟨e.1 ≫ m.1, (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso
        (e.2.prod m.2)⟩ : CommonReferenceNerve.Node (E ≫ F)) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  change (F).functor.map (δ.hom.app X ≫ e.2.hom.app X) ≫ m.2.hom.app (e.1.functor.obj X) =
    (F).functor.map (δ.hom.app X) ≫
      (F).functor.map (e.2.hom.app X) ≫ m.2.hom.app (e.1.functor.obj X)
  rw [Functor.map_comp, Category.assoc]

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E E' : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (δ : E'.functor ≅ E.functor)
local notation "J" => normalizedMap (polynomialProjection P a)
local notation "F" => BassProjectionPath.source P a

/-- Change a full reference without changing its model morphism. -/
def onReference {U W : Model.{u + 1}} {G G' : U ⟶ W}
    (ε : G'.functor ≅ G.functor) : parameterSSet G ⟶ parameterSSet G' :=
  nerveMap (Codiscrete.functorOfFun (reanchor ε))

theorem polynomial_node (e : CommonReferenceNerve.Node E) :
    postcompNode J (reanchor δ e) =
      reanchor (isoWhiskerRight δ (J).functor) (postcompNode J e) :=
  post_whiskering δ J e

theorem reference_node (e : CommonReferenceNerve.Node E) (j : Fin 5) :
    nodes P a E' (reanchor δ e) j =
      reanchor (isoWhiskerRight δ (F).functor) (nodes P a E e j) :=
  pair_whiskering F δ e (BassProjectionPath.nodes P a j)

theorem chart_node (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (e : CommonReferenceNerve.Node (E ≫ J)) :
    chartAttachmentNode P a E' α ha (reanchor (isoWhiskerRight δ (J).functor) e) =
      reanchor (isoWhiskerRight δ (F).functor) (chartAttachmentNode P a E α ha e) :=
  chart_whiskering δ J (normalizedMap (coefficientMap P (α.app a))) F
    (BassMJoin.projectionEndpointIso (c := a) P α ha) e

/-- The full polynomial attachment, before passing to native values. -/
theorem attachment : FourEdgeTree.attachment E J ≫
      onReference (isoWhiskerRight δ (J).functor) =
    onReference δ ≫ FourEdgeTree.attachment E' J := by
  have h : (fun e : CommonReferenceNerve.Node E ↦
      reanchor (isoWhiskerRight δ (J).functor) (postcompNode J e)) =
      (fun e ↦ postcompNode J (reanchor δ e)) :=
    funext fun e ↦ (polynomial_node P a E E' δ e).symm
  exact congrArg (fun f ↦ nerveMap (Codiscrete.functorOfFun f)) h

/-- Naturality of the original endpoint iso supplies both complete chart squares. -/
theorem chart (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    chartMap P a E α ha ≫ onReference (isoWhiskerRight δ (F).functor) =
      onReference (isoWhiskerRight δ (J).functor) ≫ chartMap P a E' α ha := by
  have h : (fun e : CommonReferenceNerve.Node (E ≫ J) ↦
      reanchor (isoWhiskerRight δ (F).functor) (chartAttachmentNode P a E α ha e)) =
      (fun e ↦ chartAttachmentNode P a E' α ha
        (reanchor (isoWhiskerRight δ (J).functor) e)) :=
    funext fun e ↦ (chart_node P a E E' δ α ha e).symm
  exact congrArg (fun f ↦ nerveMap (Codiscrete.functorOfFun f)) h

theorem vertex (j : Fin 5) :
    vertexMap P a E j ≫ onReference (isoWhiskerRight δ (F).functor) =
      onReference δ ≫ vertexMap P a E' j := by
  have h : (fun e : CommonReferenceNerve.Node E ↦
      reanchor (isoWhiskerRight δ (F).functor) (nodes P a E e j)) =
      (fun e ↦ nodes P a E' (reanchor δ e) j) :=
    funext fun e ↦ (reference_node P a E E' δ e j).symm
  exact congrArg (fun f ↦ nerveMap (Codiscrete.functorOfFun f)) h

/-- Every original edge retains its original simplex parameter and complete reference. -/
theorem edge (i j : Fin 5) :
    edgeMap P a E i j ≫ onReference (isoWhiskerRight δ (F).functor) =
      onReference δ ▷ Δ[1] ≫ edgeMap P a E' i j := by
  have h : (fun (e : CommonReferenceNerve.Node E) (k : Fin 2) ↦
      reanchor (isoWhiskerRight δ (F).functor) (nodes P a E e (![i, j] k))) =
      (fun e k ↦ nodes P a E' (reanchor δ e) (![i, j] k)) :=
    funext fun e ↦ funext fun k ↦ (reference_node P a E E' δ e (![i, j] k)).symm
  exact congrArg (FiniteParameter.simplicial E (reference P a E')) h

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Reanchor
