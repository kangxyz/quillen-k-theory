/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremB.VertexWeakAssembly
public import Quillen.CategoryTheory.TheoremB.CartesianProducts
public import Quillen.Topology.HomotopyPullback.Symmetry

/-! # Coordinates for the first cartesian boundary attachment

The enriched one-simplex boundary is homeomorphic to the coproduct of its
two genuine coefficient spaces. Its actual attaching map into the vertex
skeleton is exactly the pair of diagram transitions. These are geometric
inputs for the first cartesian attachment, without assuming any finite-stage
cartesian conclusion.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.CartesianRealization.Skeletal
open TheoremA

/-- Universe-compatible endpoint index. -/
abbrev Endpoint := ULift.{u} (Fin 2)

/-- Every simplex of the one-simplex boundary is constant. -/
theorem boundaryOne_constant {p : SimplexCategoryᵒᵖ}
    (a : (∂Δ[1] : SSet.{u}).obj p) (i : Fin (p.unop.len + 1)) :
    a.1.down.toOrderHom i = a.1.down.toOrderHom 0 := by
  have hn : ¬ Function.Surjective a.1.down.toOrderHom := a.2
  by_contra hne
  apply hn
  intro j
  have hle := a.1.down.toOrderHom.monotone (Fin.zero_le i)
  have htwo : ∀ x y : Fin 2, x ≤ y → y ≠ x → x = 0 ∧ y = 1 := by decide
  obtain ⟨h0, hi⟩ := htwo _ _ hle hne
  fin_cases j
  · exact ⟨0, h0⟩
  · exact ⟨i, hi⟩

/-- The actual constant boundary simplex at a chosen endpoint. -/
def boundaryOneVertex (p : SimplexCategoryᵒᵖ) (i : Fin 2) :
    (∂Δ[1] : SSet.{u}).obj p :=
  ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.const p.unop ⦋1⦌ i), by
    change ¬ Function.Surjective (fun _ : Fin (p.unop.len + 1) ↦ i)
    intro h
    obtain ⟨j, hj⟩ := h (1 - i)
    have : (i : ℕ) < 2 := i.isLt
    fin_cases i <;> simp at hj⟩

@[simp] theorem boundaryOneVertex_zero (p : SimplexCategoryᵒᵖ) (i : Fin 2) :
    (boundaryOneVertex p i).1.down.toOrderHom 0 = i := rfl

/-- Exact simplicial coproduct coordinates for an enriched one-cell boundary. -/
def boundaryOneCoproductMap (X : SSet.{u}) :
    Quillen.Realization.simplicialSigma (fun _ : Endpoint.{u} ↦ X) ⟶ diagonalSSet (outerProduct
      (∂Δ[1] : SSet.{u}) X)
      where
  app p := ↾fun z ↦ ⟨boundaryOneVertex p z.1.down, z.2⟩
  naturality _ _ _ := rfl

instance boundaryOneCoproductMap_isIso (X : SSet.{u}) :
    IsIso (boundaryOneCoproductMap X) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro p
  apply (isIso_iff_bijective _).2
  constructor
  · intro x y h
    obtain ⟨hb, hf⟩ := Sigma.ext_iff.mp h
    have hi : x.1 = y.1 := ULift.ext _ _ (congrArg (fun z ↦ z.1.down.toOrderHom 0) hb)
    exact Sigma.ext hi hf
  · intro z
    refine ⟨⟨ULift.up (z.1.1.down.toOrderHom 0), z.2⟩, ?_⟩
    apply Sigma.ext
    · apply Subtype.ext
      apply ULift.ext
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      exact (boundaryOne_constant z.1 i).symm
    · rfl

/-- The enriched boundary has the actual topological coproduct topology. -/
def boundaryOneHomeomorph (X : SSet.{u}) :
    (Σ _ : Endpoint.{u}, |X|) ≃ₜ |diagonalSSet (outerProduct (∂Δ[1] : SSet.{u}) X)| :=
  (TopCat.homeoOfIso (Quillen.Realization.realizationSigmaIso (fun _ : Endpoint.{u} ↦
    X))).symm.trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (asIso (boundaryOneCoproductMap X))))

@[simp] theorem boundaryOneHomeomorph_apply (X : SSet.{u}) (i : Endpoint.{u}) (x : |X|) :
    boundaryOneHomeomorph X ⟨i, x⟩ =
      SSet.toTop.map (Quillen.Realization.simplicialSigmaι (fun _ : Endpoint.{u} ↦ X) i ≫
        boundaryOneCoproductMap X) x
        := by
  change SSet.toTop.map (boundaryOneCoproductMap X)
    ((Quillen.Realization.realizationSigmaIso (fun _ : Endpoint.{u} ↦ X)).inv ⟨i, x⟩) = _
  rw [Quillen.Realization.realizationSigmaIso_inv_apply, Functor.map_comp]
  rfl

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The transition decorating one endpoint of an enriched edge. -/
abbrev edgeEndpointMap (s : (nerve D).nonDegenerate 1) (i : Endpoint.{u}) :=
  H.map (s.1.map (homOfLE (Fin.zero_le i.down)))

/-- In exact simplicial coordinates, each endpoint attaches by its diagram transition. -/
theorem boundaryOneCoproductMap_attaching (s : (nerve D).nonDegenerate 1) (i : Endpoint.{u}) :
    Quillen.Realization.simplicialSigmaι (fun _ : Endpoint.{u} ↦ H.obj (s.1.obj 0)) i ≫
      boundaryOneCoproductMap (H.obj (s.1.obj 0)) ≫
      diagonalMap (replacementCellAttaching H s) =
    edgeEndpointMap H s i ≫ Quillen.Realization.simplicialSigmaι (fun d : D ↦ H.obj d) (s.1.obj
      i.down) ≫
      vertexCoproductToStageOne H := by
  ext p : 3
  funext x
  apply Sigma.ext
  · apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro j k f
    dsimp
    simp only [Category.id_comp, Category.comp_id]
    change s.1.map (𝟙 _) = 𝟙 _
    exact s.1.map_id _
  · rfl

/-- The realized attaching map preserves the exact endpoint/transition coordinates. -/
theorem boundaryOneHomeomorph_attaching (s : (nerve D).nonDegenerate 1)
    (i : Endpoint.{u}) (x : |H.obj (s.1.obj 0)|) :
    SSet.toTop.map (diagonalMap (replacementCellAttaching H s))
      (boundaryOneHomeomorph (H.obj (s.1.obj 0)) ⟨i, x⟩) =
    realizedReplacementStageOneHomeomorph H
      ⟨s.1.obj i.down, SSet.toTop.map (edgeEndpointMap H s i) x⟩ := by
  rw [boundaryOneHomeomorph_apply, realizedReplacementStageOneHomeomorph_apply]
  change (SSet.toTop.map _ ≫ SSet.toTop.map _) x = (SSet.toTop.map _ ≫ SSet.toTop.map _) x
  rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, boundaryOneCoproductMap_attaching]

end Quillen.CartesianRealization.Skeletal
