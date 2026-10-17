/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputIdentityParameters
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputLowerAnchor

/-! The actual identity input is removed from the full midpoint product by its specified unitor. -/
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
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputActual
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier CommonReferenceProduct
open BassProjectionPath.WholeReference

private theorem identity_anchor_word {V W Y T Z : Type u}
    [Category.{v} V] [Category.{v} W] [Category.{v} Y]
    [Category.{v} T] [Category.{v} Z]
    (A : V ⥤ W) (E : W ⥤ Y) (Sd : Y ⥤ Z) (Sb : W ⥤ T) (L : T ⥤ Z)
    (F : V ⥤ Y) (δ : F ≅ A ⋙ E) (k : E ⋙ Sd ≅ Sb ⋙ L) :
    isoWhiskerRight (Functor.leftUnitor F).symm Sd ≪≫
      isoWhiskerRight (isoWhiskerLeft (𝟭 V) δ ≪≫
        (Functor.associator (𝟭 V) A E).symm) Sd ≪≫
      Functor.associator ((𝟭 V) ⋙ A) E Sd ≪≫
      isoWhiskerLeft ((𝟭 V) ⋙ A) k ≪≫
      (Functor.associator ((𝟭 V) ⋙ A) Sb L).symm =
    (isoWhiskerRight δ Sd ≪≫ Functor.associator A E Sd ≪≫
      isoWhiskerLeft A k ≪≫ (Functor.associator A Sb L).symm) ≪≫
        isoWhiskerRight (isoWhiskerRight (Functor.leftUnitor A).symm Sb) L := by
  apply Iso.ext
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.id_obj]
  simp

private theorem model_comp {U V W : Model.{u}} (F : U ⟶ V) (G : V ⟶ W) :
    (F ≫ G).functor = F.functor ⋙ G.functor := rfl

private theorem model_id (V : Model.{u}) : (𝟙 V : V ⟶ V).functor = 𝟭 V := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "A" => normalizedMap (coefficientMap P p)
local notation "E" => inputReference P q w
local notation "F" => TripleLaurent.input P p q w
local notation "Sb" => BassProjectionPath.source P b
local notation "Sd" => BassProjectionPath.source P d
local notation "L" => CoefficientBassLaurentCompositionCarrier.reference P q w
local notation "S" => A ≫ Sb
local notation "S₀" => InputLaurentProduct.surfaceReference P p (𝟙 (model P a))
local notation "G" => reference P d F

/-- The actual target surface uses only the inverse identity unitor on the coefficient factor. -/
def surfaceIdentity : (S).functor ≅ (S₀).functor :=
  isoWhiskerRight (Functor.leftUnitor (A).functor).symm (Sb).functor

/-- Removing the actual identity input retains the complete right-first and bottom anchor word. -/
theorem identity_anchor :
    isoWhiskerRight (Functor.leftUnitor (F).functor).symm (Sd).functor ≪≫
      InputLaurentProduct.anchor P p q w (𝟙 (model P a)) =
    InputPolynomial.midpointAnchor P p q w ≪≫
      isoWhiskerRight (surfaceIdentity P p) (L).functor := by
  have h := identity_anchor_word (A).functor (E).functor (Sd).functor (Sb).functor
    (L).functor (F).functor (TripleLaurent.inputIso P p q w)
    (InputLaurentProduct.pairAnchor P q w)
  simpa only [InputLaurentProduct.anchor, InputLaurentProduct.rightInputIso,
    InputPolynomial.midpointAnchor, surfaceIdentity, model_comp, model_id, Iso.trans_assoc] using h

/-- Every full product node uses the same explicit unitor normalization. -/
theorem identity_product (N : Node S₀) (M : Node L) :
    reanchor (isoWhiskerRight (Functor.leftUnitor (F).functor).symm (Sd).functor)
      (reanchor (InputLaurentProduct.anchor P p q w (𝟙 (model P a)))
        (node (S₀ ≫ L) S₀ L (Iso.refl _) N M)) =
    node G S L (InputPolynomial.midpointAnchor P p q w)
      (reanchor (surfaceIdentity P p) N) M := by
  rw [node_first_reanchor]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [reanchor, node, Iso.refl_trans, ← Iso.trans_assoc]
  rw [identity_anchor]

/-- The original whole midpoint product survives removal of the actual identity input. -/
theorem identity_midpoint_parameter (y : |parameterSSet S₀|) (r : I) :
    mapParameter (reanchor
      (isoWhiskerRight (Functor.leftUnitor (F).functor).symm (Sd).functor))
      (InputLaurentProduct.place P p q w (𝟙 (model P a))
        (InputLaurentProduct.product P p q w (𝟙 (model P a)) (y, r))) =
    FiniteParameter.parameter S G
      (fun N j ↦ node G S L (InputPolynomial.midpointAnchor P p q w) N
        (CoefficientBassLaurentCompositionCarrier.nodes P q w j))
      (mapParameter (reanchor (surfaceIdentity P p)) y, binaryPath (k := 2) 0 1 2 r) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter S₀ y
  change mapParameter _ (mapParameter _ (FiniteParameter.parameter _ _ _
    (CommonReferenceNerve.parameter S₀ N z, binaryPath (k := 2) 0 1 2 r))) = _
  rw [FiniteParameter.parameter_characteristic, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, FiniteParameter.parameter_characteristic]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter G ns
    (Quillen.SimplexGrid.parameter.{u + 1} k 2 (z, binaryPath (k := 2) 0 1 2 r)))
  funext i
  exact identity_product P p q w (N ((Quillen.SimplexGrid.indexEquiv k 2).symm i).1)
    (CoefficientBassLaurentCompositionCarrier.nodes P q w
      ((Quillen.SimplexGrid.indexEquiv k 2).symm i).2)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputActual
