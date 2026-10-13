/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Resolution.Covers
public import Quillen.CategoryTheory.TheoremA.ContractibleStructured
public import Mathlib.CategoryTheory.Adjunction.Comma

/-!
# The full ambient Q-subcategory on resolving objects

This is deliberately distinct from the Q-construction of the inherited exact
subcategory: the former has additional arrows whose cokernels need not lie in
the resolving subcategory. The ordinary full inclusion is treated by the dual
of Theorem A and the genuine cover category.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace Quillen.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)

/-- The resolving predicate on ambient Q-objects. -/
def qProperty : ObjectProperty E.QCategory := fun X => P X.obj.of

/-- All ambient Q-arrows between resolving objects. -/
abbrev FullQ := (qProperty E P).FullSubcategory

/-- The ordinary full-subcategory inclusion. -/
abbrev fullQInclusion : FullQ E P ⥤ E.QCategory := (qProperty E P).ι

/-- A structured comma of the full Q-inclusion. -/
abbrev FullQComma (M : C) := StructuredArrow (Q.of E.deflation E.inflation M) (fullQInclusion E P)

/-- A resolving cover determines a structured-comma object via its reverse
admissible epimorphism. -/
@[implicit_reducible]
def coverComma (M : C) (X : Cover E P M) : FullQComma E P M :=
  StructuredArrow.mk (Y := ⟨Q.of _ _ X.obj, X.property⟩) (E.qDeflation X.hom X.admissible)

/-- Cover comparisons run in the opposite direction under the Q-construction. -/
@[implicit_reducible]
def coversToComma (M : C) : (Cover E P M)ᵒᵖ ⥤ FullQComma E P M where
  obj X := coverComma E P M X.unop
  map {X Y} f := StructuredArrow.homMk
    (ObjectProperty.homMk (E.qDeflation f.unop.hom f.unop.admissible)) (by
      change E.qDeflation X.unop.hom X.unop.admissible ≫
        E.qDeflation f.unop.hom f.unop.admissible = E.qDeflation Y.unop.hom Y.unop.admissible
      rw [E.qDeflation_comp]
      simp only [f.unop.w])
  map_id X := by
    apply StructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    exact E.qDeflation_id X.unop.obj
  map_comp f g := by
    apply StructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    exact (E.qDeflation_comp _ _ _ _).symm

variable [E.IsAdmissibleSubobjectClosed P]

/-- Every comma span has a genuinely resolving apex because its right leg is
an admissible subobject of a resolving object. -/
@[implicit_reducible]
def spanCover (M : C) (A : FullQComma E P M)
    (s : Span E.deflation E.inflation M A.right.obj.obj.of) : Cover E P M :=
  ⟨s.apex, E.prop_of_inflation P s.r s.wr A.right.property, s.l, s.wl⟩

/-- The right span leg is the counit from the corresponding cover. -/
def spanCounit (M : C) (A : FullQComma E P M)
    (s : Span E.deflation E.inflation M A.right.obj.obj.of)
    (hs : Q.mkHom _ _ s = A.hom) : coverComma E P M (spanCover E P M A s) ⟶ A :=
  StructuredArrow.homMk (ObjectProperty.homMk (E.qInflation s.r s.wr))
    ((E.qSpan_factor s).symm.trans hs)

/-- The proposed terminal universal arrow, retaining the original span. -/
def spanUniversal (M : C) (A : FullQComma E P M)
    (s : Span E.deflation E.inflation M A.right.obj.obj.of)
    (hs : Q.mkHom _ _ s = A.hom) : CostructuredArrow (coversToComma E P M) A :=
  CostructuredArrow.mk (Y := op (spanCover E P M A s)) (spanCounit E P M A s hs)

/-- Factorization through the right span leg constructs the actual comparison
of covers, including its admissibility and its augmentation equation. -/
theorem spanUniversal_nonempty_hom (M : C) (A : FullQComma E P M)
    (s : Span E.deflation E.inflation M A.right.obj.obj.of)
    (hs : Q.mkHom _ _ s = A.hom)
    (V : CostructuredArrow (coversToComma E P M) A) :
    Nonempty (V ⟶ spanUniversal E P M A s hs) := by
  obtain ⟨t, ht⟩ := Quotient.exists_rep V.hom.right.hom
  change Span E.deflation E.inflation V.left.unop.obj A.right.obj.obj.of at t
  change Q.mkHom _ _ t = V.hom.right.hom at ht
  have hw := StructuredArrow.w V.hom
  change E.qDeflation V.left.unop.hom V.left.unop.admissible ≫ V.hom.right.hom = A.hom at hw
  rw [← ht, E.qDeflation_comp_span, ← hs] at hw
  obtain ⟨e, hl, hr⟩ := (Q.mkHom_eq_iff_apexIso _ _ _ _).1 hw
  change e.hom ≫ s.l = t.l ≫ V.left.unop.hom at hl
  change e.hom ≫ s.r = t.r at hr
  let f : spanCover E P M A s ⟶ V.left.unop :=
    { hom := e.inv ≫ t.l
      admissible := E.deflation_comp _ _ (E.deflation_of_iso e.symm) t.wl
      w := by
        change (e.inv ≫ t.l) ≫ V.left.unop.hom = s.l
        simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
          congrArg (fun k => e.inv ≫ k) hl.symm }
  refine ⟨CostructuredArrow.homMk f.op ?_⟩
  apply StructuredArrow.hom_ext
  apply ObjectProperty.hom_ext
  change E.qDeflation f.hom f.admissible ≫ E.qInflation s.r s.wr = V.hom.right.hom
  rw [← ht]
  refine (E.qSpan_factor
    (⟨s.apex, f.hom, s.r, f.admissible, s.wr⟩ :
      Span E.deflation E.inflation V.left.unop.obj A.right.obj.obj.of)).symm.trans ?_
  apply Q.mkHom_eq_of_apexIso _ _ _ t e.symm
  · rfl
  · simpa using (Iso.inv_comp_eq e).2 hr.symm

/-- The counit is monic on the Q-coordinate, so its universal factorization
is unique. Reverse-Q-arrows remember their actual cover maps. -/
theorem spanUniversal_hom_ext (M : C) (A : FullQComma E P M)
    (s : Span E.deflation E.inflation M A.right.obj.obj.of)
    (hs : Q.mkHom _ _ s = A.hom)
    {V : CostructuredArrow (coversToComma E P M) A}
    (f g : V ⟶ spanUniversal E P M A s hs) : f = g := by
  apply CostructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  apply Cover.Hom.ext
  apply E.qDeflation_injective f.left.unop.admissible g.left.unop.admissible
  apply (cancel_mono (E.qInflation s.r s.wr)).1
  exact (congrArg (fun k => k.right.hom) (CostructuredArrow.w f)).trans
    (congrArg (fun k => k.right.hom) (CostructuredArrow.w g)).symm

/-- The constructed universal arrow is genuinely terminal. -/
def spanUniversalIsTerminal (M : C) (A : FullQComma E P M)
    (s : Span E.deflation E.inflation M A.right.obj.obj.of)
    (hs : Q.mkHom _ _ s = A.hom) : IsTerminal (spanUniversal E P M A s hs) :=
  IsTerminal.ofUniqueHom
    (fun V => Classical.choice (spanUniversal_nonempty_hom E P M A s hs V))
    (fun _V f => spanUniversal_hom_ext E P M A s hs f _)

instance coversToComma_hasTerminals (M : C) (A : FullQComma E P M) :
    HasTerminal (CostructuredArrow (coversToComma E P M) A) := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep A.hom
  exact (spanUniversalIsTerminal E P M A s hs).hasTerminal

/-- A genuine categorical right adjoint, constructed from span apices. -/
def coverAdjunction (M : C) : coversToComma E P M ⊣
    rightAdjointOfCostructuredArrowTerminals (coversToComma E P M) :=
  adjunctionOfCostructuredArrowTerminals _

variable [E.IsExtensionClosed P]

/-- The structured comma is contractible whenever an actual resolving cover
exists. Both the cover contraction and the comparison adjunction are proved. -/
theorem fullQComma_contractible (M : C) (B : Cover E P M) :
    ContractibleSpace (ClassifyingSpace (FullQComma E P M)) := by
  let := Cover.contractible B
  let : ContractibleSpace (ClassifyingSpace (Cover E P M)ᵒᵖ) :=
    (TopCat.homeoOfIso (classifyingOppositeIso (Cover E P M))).toHomotopyEquiv.contractibleSpace
  exact (adjunctionClassifyingHomotopyEquiv (coverAdjunction E P M)).symm.contractibleSpace

/-- The full ambient Q-subcategory is homotopy equivalent to ambient Q under
admissible-subobject closure and actual admissible epimorphic covers. -/
def fullQClassifyingHomotopyEquiv (h : ∀ M, Nonempty (Cover E P M)) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (FullQ E P)) E.KSpace :=
  TheoremA.contractibleStructuredClassifyingHomotopyEquiv (fullQInclusion E P)
    (fun M => fullQComma_contractible E P M.obj.of (Classical.choice (h M.obj.of)))

@[simp] theorem fullQClassifyingHomotopyEquiv_toFun
    (h : ∀ M, Nonempty (Cover E P M)) :
    (fullQClassifyingHomotopyEquiv E P h).toFun =
      (classifyingSpaceMap (fullQInclusion E P)).hom := rfl

omit [E.IsAdmissibleSubobjectClosed P] [E.IsExtensionClosed P] in
/-- Actual finite-resolution data always supplies the epimorphic covers.
Admissible-subobject closure remains a separate, genuinely stronger condition. -/
theorem covers_of_finiteResolutions (h : E.ResolutionHypothesis P) (M : C) :
    Nonempty (Cover E P M) := by
  obtain ⟨R⟩ := h M
  obtain ⟨Y, p, hY, hp⟩ := R.presentation
  exact ⟨⟨Y, hY, p, hp⟩⟩

end Quillen.Resolution
