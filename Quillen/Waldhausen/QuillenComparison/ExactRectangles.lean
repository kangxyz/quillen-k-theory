import Quillen.Waldhausen.ExactCategory
import Quillen.CategoryTheory.ExactCategory.SpecialFractions

/-!
# Exact rectangles in the genuine S-construction

For an exact category, every quotient map in an S-simplex is an admissible
epimorphism. The overlapping quotient rectangles are pullbacks, not just
commuting squares. These are the universal properties used to compose the
span representatives of the Quillen comparison.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- A pushout whose lower-left vertex is zero supplies the actual cokernel
universal property of its upper edge. -/
def cokernelOfZeroPushout {A B Z D : C} {i : A ⟶ B} {z : A ⟶ Z}
    {p : B ⟶ D} {q : Z ⟶ D} (sq : IsPushout i z p q) (hZ : IsZero Z) :
    IsColimit (CokernelCofork.ofπ p (show i ≫ p = 0 from by
      rw [sq.w, hZ.eq_of_src q 0, comp_zero])) := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {W} f hf ↦ sq.desc f 0 (by simpa using hf)) ?_ ?_
  · intro W f hf
    exact sq.inl_desc _ _ _
  · intro W f hf m hm
    apply sq.hom_ext
    · simpa using hm
    · exact hZ.eq_of_src _ _

variable (E : Quillen.ExactStructure C)
variable {n : SimplexCategory} {F : Grid n ⥤ C}
variable (hF : IsSimplex E.inflation (MorphismProperty.isomorphisms C) F)

/-- The arrow in one row between comparable interval objects. -/
def rowMap (t : Fin (n.len + 1)) {i j k l : Fin (n.len + 1)}
    (hij : i ≤ j) (hkl : k ≤ l) (hik : i ≤ k) (hjl : j ≤ l) :
    F.obj (grid t i j hij) ⟶ F.obj (grid t k l hkl) :=
  F.map (homOfLE (show grid t i j hij ≤ grid t k l hkl from
    ⟨le_rfl, hik, hjl⟩))

@[simp]
theorem rowMap_id (t : Fin (n.len + 1)) {i j : Fin (n.len + 1)} (hij : i ≤ j) :
    rowMap (F := F) t hij hij le_rfl le_rfl = 𝟙 _ := F.map_id _

@[reassoc (attr := simp)]
theorem rowMap_comp (t : Fin (n.len + 1)) {i j k l a b : Fin (n.len + 1)}
    (hij : i ≤ j) (hkl : k ≤ l) (hab : a ≤ b)
    (hik : i ≤ k) (hjl : j ≤ l) (hka : k ≤ a) (hlb : l ≤ b) :
    rowMap (F := F) t hij hkl hik hjl ≫ rowMap (F := F) t hkl hab hka hlb =
      rowMap (F := F) t hij hab (hik.trans hka) (hjl.trans hlb) :=
  (F.map_comp _ _).symm

include hF

/-- The two consecutive quotient arrows in an S-row compose to zero. -/
theorem rowMap_zero (t i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    rowMap (F := F) t hij (hij.trans hjk) le_rfl hjk ≫
      rowMap (F := F) t (hij.trans hjk) hjk hij le_rfl = 0 := by
  have sq := hF.quotient t i j k hij hjk
  calc
    _ = rowMap (F := F) t hij le_rfl hij le_rfl ≫
        rowMap (F := F) t le_rfl hjk le_rfl hjk := sq.w
    _ = 0 := by
      have hz : rowMap (F := F) t (i := j) le_rfl hjk le_rfl hjk = 0 :=
        (hF.zero t j).eq_of_src _ _
      rw [hz, comp_zero]

/-- Every triple of ordered indices gives a conflation in the original
exact structure, with precisely the maps already present in the S-simplex. -/
theorem row_conflation (t i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    E.conflation (ShortComplex.mk
      (rowMap (F := F) t hij (hij.trans hjk) le_rfl hjk)
      (rowMap (F := F) t (hij.trans hjk) hjk hij le_rfl)
      (rowMap_zero E hF t i j k hij hjk)) := by
  exact E.conflation_of_inflation_of_isCokernel
    (hF.cofibration t i j k hij hjk)
    (cokernelOfZeroPushout (hF.quotient t i j k hij hjk) (hF.zero t j))

/-- Quotient maps in an S-row are admissible epimorphisms. -/
theorem row_deflation (t i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    E.deflation (rowMap (F := F) t (hij.trans hjk) hjk hij le_rfl) :=
  E.deflation_of_conflation (row_conflation E hF t i j k hij hjk)

/-- An overlapping rectangle of subquotients is a genuine pullback. -/
theorem row_isPullback (t i j k l : Fin (n.len + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    IsPullback
      (rowMap (F := F) t (hij.trans hjk) (hij.trans (hjk.trans hkl)) le_rfl hkl)
      (rowMap (F := F) t (hij.trans hjk) hjk hij le_rfl)
      (rowMap (F := F) t (hij.trans (hjk.trans hkl)) (hjk.trans hkl) hij le_rfl)
      (rowMap (F := F) t hjk (hjk.trans hkl) le_rfl hkl) := by
  apply E.isPullback_of_conflations_same_kernel
    (row_conflation E hF t i j k hij hjk)
    (row_conflation E hF t i j l hij (hjk.trans hkl))
  · simp
  · simp

end Quillen.Waldhausen.QuillenComparison
