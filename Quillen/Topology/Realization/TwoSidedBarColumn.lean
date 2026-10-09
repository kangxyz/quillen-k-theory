import Quillen.Topology.Realization.TwoSidedBarResolution

/-! # The actual transposed bar row is a nerve

An indexing chain and its first coefficient determine all coefficient
objects by transport. Its final augmentation determines every earlier
augmentation by composition. This identifies the literal bar row with the
nerve of the genuine elementary resolution category.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u

namespace Quillen.TwoSidedBar
open TheoremA
variable (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (q : SimplexCategoryᵒᵖ)

@[simp] theorem Resolution.eqToHom_map {a b : Resolution H q} (h : a = b) :
    (eqToHom h : a ⟶ b).map = eqToHom (congrArg Resolution.index h) := by
  cases h
  rfl

instance Resolution.forget_faithful : (Resolution.forget H q).Faithful where
  map_injective h := Resolution.Hom.ext h

/-- Reconstruct the full augmented coefficient chain from the literal bar
coordinates. -/
def resolutionChain {p : SimplexCategoryᵒᵖ} (z : ((bar H).obj p).obj q) :
    ComposableArrows (Resolution H q) p.unop.len where
  obj i := {
    index := z.1.obj i
    value := (H.map (indexProjection.map (z.1.map (homOfLE (Fin.zero_le i))))).app q z.2.1
    arrow := indexProjection.map (z.1.map (homOfLE (Fin.le_last i))) ≫ z.2.2.down.op }
  map {i j} f := {
    map := z.1.map f
    value := by
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← H.map_comp,
        ← indexProjection.map_comp, ← z.1.map_comp]
      rfl
    arrow := by
      rw [← Category.assoc, ← indexProjection.map_comp, ← z.1.map_comp]
      rfl }
  map_id i := by apply Resolution.Hom.ext; exact z.1.map_id i
  map_comp f g := by apply Resolution.Hom.ext; exact z.1.map_comp f g

/-- Recover the original indexing chain, first coefficient, and final arrow. -/
def resolutionCoordinates {p : SimplexCategoryᵒᵖ}
    (F : ComposableArrows (Resolution H q) p.unop.len) : ((bar H).obj p).obj q :=
  ⟨F ⋙ Resolution.forget H q, (F.obj 0).value,
    ULift.up (F.obj (Fin.last p.unop.len)).arrow.unop⟩

/-- Recovering the bar coordinates after reconstruction changes no coordinate. -/
theorem resolutionCoordinates_chain {p : SimplexCategoryᵒᵖ}
    (z : ((bar H).obj p).obj q) :
    resolutionCoordinates H q (resolutionChain H q z) = z := by
  cases z with
  | mk s z =>
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply Prod.ext
    · change (H.map (indexProjection.map (s.map (𝟙 (0 : Fin (p.unop.len + 1)))))).app q z.1 = z.1
      rw [s.map_id, indexProjection.map_id, H.map_id]
      rfl
    · apply ULift.ext
      change (indexProjection.map (s.map (𝟙 (Fin.last p.unop.len))) ≫ z.2.down.op).unop = z.2.down
      rw [s.map_id, indexProjection.map_id, Category.id_comp]
      rfl

/-- Every resolution chain is recovered, using its genuine coefficient and
augmentation compatibility equations. -/
theorem resolutionChain_coordinates {p : SimplexCategoryᵒᵖ}
    (F : ComposableArrows (Resolution H q) p.unop.len) :
    resolutionChain H q (resolutionCoordinates H q F) = F := by
  have hobj (i : Fin (p.unop.len + 1)) :
      (resolutionChain H q (resolutionCoordinates H q F)).obj i = F.obj i := by
    refine Resolution.ext (by rfl) ?_ ?_
    · exact heq_of_eq (F.map (homOfLE (Fin.zero_le i))).value
    · exact heq_of_eq (F.map (homOfLE (Fin.le_last i))).arrow
  refine CategoryTheory.Functor.ext hobj ?_
  intro i j f
  apply Resolution.Hom.ext
  change (F.map f).map = (eqToHom (hobj i)).map ≫ (F.map f).map ≫
    (eqToHom (hobj j).symm).map
  simp only [Resolution.eqToHom_map, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The literal coordinate equivalence in each outer degree. -/
def columnEquiv (p : SimplexCategoryᵒᵖ) :
    (nerve (Resolution H q)).obj p ≃ ((bar H).flip.obj q).obj p where
  toFun := resolutionCoordinates H q
  invFun := resolutionChain H q
  left_inv := resolutionChain_coordinates H q
  right_inv := resolutionCoordinates_chain H q

/-- This coordinate identification commutes with every outer ordinal map. -/
def columnIso : nerve (Resolution H q) ≅ (bar H).flip.obj q :=
  NatIso.ofComponents (fun p ↦ (columnEquiv H q p).toIso) (by
    intro p r α
    ext F : 3
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply Prod.ext
    · exact (F.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0)))).value.symm
    · apply ULift.ext
      exact congrArg Quiver.Hom.unop
        (F.map (homOfLE (Fin.le_last (α.unop.toOrderHom (Fin.last r.unop.len))))).arrow.symm)

end Quillen.TwoSidedBar
