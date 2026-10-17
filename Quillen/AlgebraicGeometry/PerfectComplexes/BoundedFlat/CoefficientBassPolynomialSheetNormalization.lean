/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenMap
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! Full reference normalization of the actual polynomial cap's first sheet. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPolynomialSheetNormalization
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {V W T : Model.{u}} (F F' : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (ε : G.functor ≅ (F ≫ J).functor) (δ : F'.functor ≅ F.functor)

/-- The Laurent iso retains both the polynomial normalization and the old whole anchor. -/
def laurentIso : (F' ≫ J).functor ≅ G.functor :=
  isoWhiskerRight δ J.functor ≪≫ ε.symm

/-- The ordinary attachment square is proved on every complete dependent reference node. -/
theorem attachment_node (N : Node F) :
    CommonReferenceProduct.reanchor (laurentIso F F' J G ε δ)
      (attachPostcompNode F J G ε N) =
    attachPostcompNode F' J (F' ≫ J) (Iso.refl _)
      (CommonReferenceProduct.reanchor δ N) := by
  rcases N with ⟨K, ρ⟩
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [laurentIso, CommonReferenceProduct.reanchor, attachPostcompNode,
    Iso.refl_trans, isoWhiskerRight_trans, Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- The same attachment equality holds over the entire realized polynomial reference nerve. -/
theorem attachment_parameter (y : |parameterSSet F|) :
    mapParameter (CommonReferenceProduct.reanchor (laurentIso F F' J G ε δ))
      (mapParameter (attachPostcompNode F J G ε) y) =
    mapParameter (attachPostcompNode F' J (F' ≫ J) (Iso.refl _))
      (mapParameter (CommonReferenceProduct.reanchor δ) y) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  rw [mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns ↦ parameter (F' ≫ J) ns z)
    (funext (fun i ↦ attachment_node F F' J G ε δ (N i)))

/-- The actual whole attachment square supplies the first displayed pushout map. -/
theorem attachment_square :
    SSet.toTop.map (attaching F J G ε) ≫
      TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor
        (laurentIso F F' J G ε δ))) =
    TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor δ)) ≫
      SSet.toTop.map (attaching F' J (F' ≫ J) (Iso.refl _)) := by
  ext y
  exact attachment_parameter F F' J G ε δ y

/-- This is the original single-sheet map, with the same cylinder height and terminal tip. -/
def map : C(|firstSimplicial F J G ε|,
    |firstSimplicial F' J (F' ≫ J) (Iso.refl _)|) :=
  (CommonReferenceNerve.CutOpenMap.firstMap F J G F' J (F' ≫ J) ε (Iso.refl _)
    (TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor δ)))
    (TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor
      (laurentIso F F' J G ε δ)))) (attachment_square F F' J G ε δ)).hom

end Quillen.PerfectComplexes.CoefficientBassPolynomialSheetNormalization
