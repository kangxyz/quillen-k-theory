/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputCentralBottom
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputLowerParameter

/-! Source precomposition retains the entire frozen central midpoint product. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputCentral
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier CommonReferenceProduct

private theorem precomp_product_node {U V W X Y : Model.{v}}
    (A : U ⟶ V) (E : V ⟶ W) (Sd : W ⟶ Y) (B : V ⟶ X) (L : X ⟶ Y) (G : U ⟶ Y)
    (δ : G.functor ≅ ((A ≫ E) ≫ Sd).functor)
    (k : (E ≫ Sd).functor ≅ (B ≫ L).functor) (N : Node B) (M : Node L) :
    reanchor δ (precompNode A (node (E ≫ Sd) B L k N M)) =
      node G (A ≫ B) L (δ ≪≫ Functor.associator A.functor E.functor Sd.functor ≪≫
        isoWhiskerLeft A.functor k ≪≫ (Functor.associator A.functor B.functor L.functor).symm)
        (precompNode A N) M := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext x
  simp only [reanchor, precompNode, node, BassReferenceMerge.composition_pair_iso,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app, Iso.symm_hom,
    Functor.associator_inv_app, Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "A" => normalizedMap (coefficientMap P p)
local notation "E" => inputReference P q w
local notation "F" => TripleLaurent.input P p q w
local notation "Sb" => BassProjectionPath.source P b
local notation "Sd" => BassProjectionPath.source P d
local notation "L" => CoefficientBassLaurentCompositionCarrier.reference P q w
local notation "G" => BassProjectionPath.WholeReference.reference P d F

/-- Each transported old bottom node is the same full midpoint composition node. -/
theorem transported_bottom_node (N : Node Sb) (M : Node L) :
    reanchor (isoWhiskerRight (TripleLaurent.inputIso P p q w) (Sd).functor)
      (precompNode A (node (E ≫ Sd) Sb L (InputLaurentProduct.pairAnchor P q w) N M)) =
    node G (A ≫ Sb) L (InputPolynomial.midpointAnchor P p q w) (precompNode A N) M :=
  precomp_product_node A E Sd Sb L G
    (isoWhiskerRight (TripleLaurent.inputIso P p q w) (Sd).functor)
    (InputLaurentProduct.pairAnchor P q w) N M

/-- The unchanged frozen central bottom retains both scalar times after the actual input map. -/
theorem transported_bottom_parameter (r t : I) :
    laurentMap P p q w (laurentCube P q w (r, (0, t))) =
      InputPolynomial.midpointProduct P p q w
        (mapParameter (precompNode A) (CommonReferenceNerve.parameter Sb
          (BassProjectionPath.nodes P b) (BassProjectionPath.parameter t)), r) := by
  rw [bottom_product_parameter]
  change mapParameter _ (mapParameter _ (FiniteParameter.parameter _ _ _
    (CommonReferenceNerve.parameter Sb (BassProjectionPath.nodes P b)
      (BassProjectionPath.parameter t), binaryPath (k := 2) 0 1 2 r))) = _
  rw [FiniteParameter.parameter_characteristic, mapParameter_parameter, mapParameter_parameter]
  change _ = FiniteParameter.parameter (A ≫ Sb) G _
    (mapParameter (precompNode A) (CommonReferenceNerve.parameter Sb
      (BassProjectionPath.nodes P b) (BassProjectionPath.parameter t)),
      binaryPath (k := 2) 0 1 2 r)
  rw [mapParameter_parameter, FiniteParameter.parameter_characteristic]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter G ns
    (Quillen.SimplexGrid.parameter 4 2
      (BassProjectionPath.parameter t, binaryPath (k := 2) 0 1 2 r)))
  funext i
  exact transported_bottom_node P p q w
    (BassProjectionPath.nodes P b ((Quillen.SimplexGrid.indexEquiv 4 2).symm i).1)
    (CoefficientBassLaurentCompositionCarrier.nodes P q w
      ((Quillen.SimplexGrid.indexEquiv 4 2).symm i).2)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputCentral
