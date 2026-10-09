import Quillen.Waldhausen.Approximation.WeakFlags
import Quillen.Waldhausen.QuillenComparison.FlagPresentation

/-!
# Weak-equivalence categories of genuine quotient rows

Objects retain actual zero diagonals, cofibration maps and quotient
pushouts. Morphisms are pointwise weak-equivalence natural transformations.
Canonical cokernel completion is defined on the actual weak-map flag
category, with weak-equivalence preservation proved using Waldhausen gluing.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v u

namespace Quillen.Waldhausen

open QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- An exact quotient row whose horizontal cofibrations lie in the stated class. -/
@[ext]
structure WeakRow (E : Quillen.ExactStructure C) (cof weq : MorphismProperty C)
    (n : SimplexCategory) where
  row : Row E n
  cofibration (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    cof (row.diagram.map (homOfLE
      (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl, hjk⟩)))

namespace WeakRow

variable {E : Quillen.ExactStructure C} {cof weq : MorphismProperty C}
  {n : SimplexCategory} [weq.IsMultiplicative]

instance : Category (WeakRow E cof weq n) where
  Hom F G := { α : F.row.diagram ⟶ G.row.diagram // ∀ p, weq (α.app p) }
  id F := ⟨𝟙 F.row.diagram, fun _ ↦ weq.id_mem _⟩
  comp α β := ⟨α.val ≫ β.val, fun p ↦ weq.comp_mem _ _ (α.property p) (β.property p)⟩
  id_comp α := Subtype.ext (Category.id_comp α.val)
  comp_id α := Subtype.ext (Category.comp_id α.val)
  assoc α β γ := Subtype.ext (Category.assoc α.val β.val γ.val)

@[ext]
theorem hom_ext {F G : WeakRow E cof weq n} {α β : F ⟶ G} (h : α.val = β.val) : α = β :=
  Subtype.ext h

/-- The genuine initial flag, including its pointwise weak-equivalence morphisms. -/
def initialFlagFunctor : WeakRow E cof weq n ⥤ WeakFlag cof weq n.len where
  obj F := {
    diagram := initialFlag E F.row
    zero := initialFlag_zero E F.row
    cofibration f := F.cofibration 0 _ _ (Fin.zero_le _) (leOfHom f) }
  map α := ⟨Functor.whiskerLeft (initialIntervals n) α.val,
    fun i ↦ α.property (interval 0 i (Fin.zero_le _))⟩

/-- The actual inclusion when the horizontal-cofibration class is enlarged. -/
def inclusion (cof' : MorphismProperty C) (h : cof ≤ cof') :
    WeakRow E cof weq n ⥤ WeakRow E cof' weq n where
  obj F := ⟨F.row, fun i j k hij hjk ↦ h _ (F.cofibration i j k hij hjk)⟩
  map α := α

end WeakRow

section Completion

variable (E : Quillen.ExactStructure C) (W V : Structure C)
  (hWE : W.cof ≤ E.inflation) (hEV : E.inflation ≤ V.cof) {n : SimplexCategory}

include hEV in
/-- Canonical quotient transformations preserve weak equivalences by gluing
actual cokernel pushouts along the actual flag cofibrations. -/
theorem quotientNatTrans_weak {A B : Fin (n.len + 1) ⥤ C}
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
    (hB : ∀ {i j} (f : i ⟶ j), E.inflation (B.map f))
    (α : A ⟶ B) (hα : ∀ i, V.weq (α.app i)) (p : Interval n) :
    V.weq ((quotientNatTrans E hA hB α).app p) := by
  let q := (quotientNatTrans E hA hB α).app p
  have hP := isPushoutOfZeroCokernel (flagQuotient_zero E hA p)
    (flagQuotient_isCokernel E hA p) V.isZero
    (0 : A.obj p.1.1 ⟶ V.zero) (0 : V.zero ⟶ _)
  have hP' := isPushoutOfZeroCokernel (flagQuotient_zero E hB p)
    (flagQuotient_isCokernel E hB p) V.isZero
    (0 : B.obj p.1.1 ⟶ V.zero) (0 : V.zero ⟶ _)
  exact V.gluing (α.app p.1.1) (α.app p.1.2) (𝟙 V.zero) q
    (hEV _ (hA _)) (hEV _ (hB _)) hP hP'
    (α.naturality _) (by simp) (flagQuotient_quotientNatTrans E hA hB α p)
    (by simp) (hα _) (hα _) (V.weq.id_mem _)

/-- Completion's horizontal maps are cobase changes in the chosen
Waldhausen cofibration class, not merely ambient exact inflations. -/
theorem quotientDiagram_cofibration (A : Fin (n.len + 1) ⥤ C)
    (hA : ∀ {i j} (f : i ⟶ j), W.cof (A.map f))
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    W.cof ((quotientDiagram E A (fun f ↦ hWE _ (hA f))).map
      (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl, hjk⟩))) := by
  let {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
    hasCokernel_of_inflation E (A.map f) (hWE _ (hA f))
  have sq := quotient_isPushout (A.map (homOfLE hij)) (A.map (homOfLE hjk))
    (A.map (homOfLE (hij.trans hjk))) (by rw [← A.map_comp]; rfl)
  have hi := W.cof_pushout (hA (homOfLE hjk)) sq
  change W.cof (cokernel.map (A.map (homOfLE hij))
    (A.map (homOfLE (hij.trans hjk))) (A.map (𝟙 i)) (A.map (homOfLE hjk))
      (by simp only [← A.map_comp]; congr 1))
  simpa only [A.map_id, quotientInclusion] using hi

/-- Canonical completion on actual weak-equivalence flag categories. -/
def completeFlags : WeakFlag W.cof V.weq n.len ⥤ WeakRow E W.cof V.weq n where
  obj F := {
    row := flagRow E F.diagram (fun f ↦ hWE _ (F.cofibration f))
    cofibration := quotientDiagram_cofibration E W hWE F.diagram F.cofibration }
  map {F G} α := ⟨quotientNatTrans E
    (fun f ↦ hWE _ (F.cofibration f)) (fun f ↦ hWE _ (G.cofibration f)) α.val,
    quotientNatTrans_weak E V hEV
      (fun f ↦ hWE _ (F.cofibration f)) (fun f ↦ hWE _ (G.cofibration f)) α.val α.property⟩
  map_id F := Subtype.ext (quotientNatTrans_id E (fun f ↦ hWE _ (F.cofibration f)))
  map_comp {F G H} α β := Subtype.ext (quotientNatTrans_comp E
    (fun f ↦ hWE _ (F.cofibration f)) (fun f ↦ hWE _ (G.cofibration f))
    (fun f ↦ hWE _ (H.cofibration f)) α.val β.val)

end Completion

end Quillen.Waldhausen
