import Quillen.Waldhausen.QuillenComparison.RowGroupoid

/-! # Recovering quotient-row isomorphisms from initial flags

Every interval quotient is the actual cokernel of the corresponding map in
the initial flag. Thus a natural isomorphism of initial flags extends to the
whole quotient row, uniquely by cokernel descent.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

/-- The initial intervals [0,i] in a simplex. -/
def initialIntervals (n : SimplexCategory) : Fin (n.len + 1) ⥤ Interval n :=
  (show Monotone (fun i : Fin (n.len + 1) ↦ interval 0 i (Fin.zero_le i)) from
    fun _ _ h ↦ ⟨le_rfl, h⟩).functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)
variable {n : SimplexCategory}

/-- The initial flag underlying an exact quotient row. -/
def initialFlag (F : Row E n) : Fin (n.len + 1) ⥤ C := initialIntervals n ⋙ F.diagram

/-- The canonical quotient arrow from the initial flag to an interval object. -/
def initialQuotient (F : Row E n) (p : Interval n) :
    (initialFlag E F).obj p.1.2 ⟶ F.diagram.obj p :=
  F.diagram.map (homOfLE ⟨Fin.zero_le _, le_rfl⟩)

/-- Every interval of the row is a specified cokernel of an initial-flag arrow. -/
def initialCofork (F : Row E n) (p : Interval n) :
    CokernelCofork ((initialFlag E F).map (homOfLE p.2)) :=
  CokernelCofork.ofπ (initialQuotient E F p) (rowMap_zero E F.simplex 0 0 p.1.1 p.1.2 (Fin.zero_le _) p.2)

/-- Its universal property is a proved consequence of the original S-pushout. -/
def initialCokernel (F : Row E n) (p : Interval n) : IsColimit (initialCofork E F p) :=
  E.cokernel _ (row_conflation E F.simplex 0 0 p.1.1 p.1.2 (Fin.zero_le _) p.2)

/-- An initial-flag isomorphism induces an isomorphism at every quotient interval. -/
def flagIsoAt {F G : Row E n} (e : initialFlag E F ≅ initialFlag E G) (p : Interval n) :
    F.diagram.obj p ≅ G.diagram.obj p :=
  CokernelCofork.mapIsoOfIsColimit (initialCokernel E F p) (initialCokernel E G p)
    (Arrow.isoMk (e.app p.1.1) (e.app p.1.2) (e.hom.naturality (homOfLE p.2)).symm)

@[reassoc (attr := simp)]
theorem initialQuotient_flagIsoAt {F G : Row E n}
    (e : initialFlag E F ≅ initialFlag E G) (p : Interval n) :
    initialQuotient E F p ≫ (flagIsoAt E e p).hom =
      e.hom.app p.1.2 ≫ initialQuotient E G p :=
by
  dsimp only [flagIsoAt, CokernelCofork.mapIsoOfIsColimit, CokernelCofork.mapOfIsColimit]
  exact (initialCokernel E F p).fac _ WalkingParallelPair.one

/-- Quotient descent commutes with every map of intervals. -/
theorem flagIsoAt_naturality {F G : Row E n}
    (e : initialFlag E F ≅ initialFlag E G) {p q : Interval n} (f : p ⟶ q) :
    F.diagram.map f ≫ (flagIsoAt E e q).hom = (flagIsoAt E e p).hom ≫ G.diagram.map f := by
  let : Epi (initialQuotient E F p) := Cofork.IsColimit.epi (initialCokernel E F p)
  apply (cancel_epi (initialQuotient E F p)).1
  have hF : initialQuotient E F p ≫ F.diagram.map f =
      (initialFlag E F).map (homOfLE (leOfHom f).2) ≫ initialQuotient E F q := by
    simp only [initialQuotient, initialFlag, CategoryTheory.Functor.comp_map, ← F.diagram.map_comp]
    congr 1
  have hG : initialQuotient E G p ≫ G.diagram.map f =
      (initialFlag E G).map (homOfLE (leOfHom f).2) ≫ initialQuotient E G q := by
    simp only [initialQuotient, initialFlag, CategoryTheory.Functor.comp_map, ← G.diagram.map_comp]
    congr 1
  calc
    _ = (initialFlag E F).map (homOfLE (leOfHom f).2) ≫
        initialQuotient E F q ≫ (flagIsoAt E e q).hom := by rw [← Category.assoc, hF, Category.assoc]
    _ = (initialFlag E F).map (homOfLE (leOfHom f).2) ≫
        e.hom.app q.1.2 ≫ initialQuotient E G q := by rw [initialQuotient_flagIsoAt]
    _ = e.hom.app p.1.2 ≫ (initialFlag E G).map (homOfLE (leOfHom f).2) ≫
        initialQuotient E G q := by rw [← Category.assoc, e.hom.naturality, Category.assoc]
    _ = e.hom.app p.1.2 ≫ initialQuotient E G p ≫ G.diagram.map f := by rw [hG]
    _ = _ := by rw [← Category.assoc, ← initialQuotient_flagIsoAt, Category.assoc]

/-- The unique extension of an isomorphism of initial flags to all quotients. -/
def extendFlagIso {F G : Row E n} (e : initialFlag E F ≅ initialFlag E G) : F ⟶ G :=
  NatIso.ofComponents (flagIsoAt E e) (fun f ↦ flagIsoAt_naturality E e f)

end Quillen.Waldhausen.QuillenComparison
