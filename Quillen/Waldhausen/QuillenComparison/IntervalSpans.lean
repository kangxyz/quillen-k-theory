import Quillen.Waldhausen.QuillenComparison.ExactRectangles
import Quillen.CategoryTheory.QConstruction.Basic

/-!
# The canonical subquotient-span functor

A row of an exact S-simplex canonically assigns a Quillen Q-morphism to an
inclusion of intervals. The apex is the intervening subquotient. Composition
is proved by the genuine pullback squares of `ExactRectangles`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v u

namespace Quillen.Waldhausen.QuillenComparison

/-- Intervals ordered by containment: the left endpoint reverses direction. -/
def NestedInterval (n : SimplexCategory) :=
  { p : (Fin (n.len + 1))ᵒᵈ × Fin (n.len + 1) // OrderDual.ofDual p.1 ≤ p.2 }

instance (n : SimplexCategory) : PartialOrder (NestedInterval n) :=
  inferInstanceAs (PartialOrder { p : (Fin (n.len + 1))ᵒᵈ × Fin (n.len + 1) //
    OrderDual.ofDual p.1 ≤ p.2 })

namespace NestedInterval

variable {n : SimplexCategory}

def left (p : NestedInterval n) : Fin (n.len + 1) := OrderDual.ofDual p.1.1

def right (p : NestedInterval n) : Fin (n.len + 1) := p.1.2

theorem endpoints (p : NestedInterval n) : p.left ≤ p.right := p.2

theorem left_anti {p q : NestedInterval n} (h : p ≤ q) : q.left ≤ p.left := h.1

theorem right_mono {p q : NestedInterval n} (h : p ≤ q) : p.right ≤ q.right := h.2

end NestedInterval

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)
variable {n : SimplexCategory} {F : Grid n ⥤ C}
variable (hF : IsSimplex E.inflation (MorphismProperty.isomorphisms C) F)

/-- The object associated to an interval is its already specified quotient. -/
def rowObject (t : Fin (n.len + 1)) (p : NestedInterval n) : C :=
  F.obj (grid t p.left p.right p.endpoints)

/-- The canonical admissible span associated to interval containment. -/
def intervalSpan (t : Fin (n.len + 1)) {p q : NestedInterval n} (h : p ≤ q) :
    Span E.deflation E.inflation (rowObject (F := F) t p) (rowObject (F := F) t q) where
  apex := F.obj (grid t q.left p.right ((NestedInterval.left_anti h).trans p.endpoints))
  l := rowMap t ((NestedInterval.left_anti h).trans p.endpoints) p.endpoints (NestedInterval.left_anti h) le_rfl
  r := rowMap t ((NestedInterval.left_anti h).trans p.endpoints) q.endpoints le_rfl (NestedInterval.right_mono h)
  wl := row_deflation E hF t q.left p.left p.right (NestedInterval.left_anti h) p.endpoints
  wr := hF.cofibration t q.left p.right q.right
    ((NestedInterval.left_anti h).trans p.endpoints) (NestedInterval.right_mono h)

/-- The span of an identity containment represents the identity Q-morphism. -/
@[simp]
theorem intervalSpan_id (t : Fin (n.len + 1)) (p : NestedInterval n) :
    Q.mkHom E.deflation E.inflation (intervalSpan E hF t (le_refl p)) =
      𝟙 (Q.of E.deflation E.inflation (rowObject (F := F) t p)) := by
  change Q.mkHom _ _ _ = Q.mkHom _ _ (Span.id _)
  refine Q.mkHom_eq_of_apexIso E.deflation E.inflation
    (intervalSpan E hF t (le_refl p)) (Span.id _) (Iso.refl _) ?_ ?_
  · simp [intervalSpan, rowMap]
  · simp [intervalSpan, rowMap]

/-- The pullback defining composition of canonical spans is the intervening
subquotient. Therefore the represented Q-arrows compose exactly. -/
@[reassoc (attr := simp)]
theorem intervalSpan_comp (t : Fin (n.len + 1)) {p q r : NestedInterval n}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    Q.mkHom E.deflation E.inflation (intervalSpan E hF t hpq) ≫
      Q.mkHom E.deflation E.inflation (intervalSpan E hF t hqr) =
        Q.mkHom E.deflation E.inflation (intervalSpan E hF t (hpq.trans hqr)) := by
  let sq := (row_isPullback E hF t r.left q.left p.right q.right
    (NestedInterval.left_anti hqr) ((NestedInterval.left_anti hpq).trans p.endpoints) (NestedInterval.right_mono hpq)).flip
  letI := sq.hasPullback
  symm
  apply Q.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst _ _ ≫ _ = _
    rw [← Category.assoc, sq.isoPullback_hom_fst]
    simp only [intervalSpan, rowMap, ← F.map_comp]
    congr 1
  · change sq.isoPullback.hom ≫ pullback.snd _ _ ≫ _ = _
    rw [← Category.assoc, sq.isoPullback_hom_snd]
    simp only [intervalSpan, rowMap, ← F.map_comp]
    congr 1

/-- A genuine S-row defines a functor from interval containment to the
existing Quillen category. Neither category is redefined for this comparison. -/
def intervalQFunctor (t : Fin (n.len + 1)) : NestedInterval n ⥤ Q E.deflation E.inflation where
  obj p := Q.of E.deflation E.inflation (rowObject (F := F) t p)
  map f := Q.mkHom E.deflation E.inflation (intervalSpan E hF t (leOfHom f))
  map_id p := intervalSpan_id E hF t p
  map_comp f g := (intervalSpan_comp E hF t (leOfHom f) (leOfHom g)).symm

end Quillen.Waldhausen.QuillenComparison
