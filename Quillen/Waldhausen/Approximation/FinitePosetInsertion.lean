/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.FinitePosetColimits
import Quillen.Waldhausen.Approximation.FactorizationData

/-!
# Inserting an actual maximal vertex from its latching cocone

A cocone on the strict lower boundary extends an existing diagram on the
complement of a maximal vertex. The extension retains all old objects and
arrows. All incoming maps are the actual latching cocone legs, and a specified
old comparison extends naturally from its strictly compatible boundary map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen
open Quillen.FinitePosetLatching
universe w w' z u v u' v'

namespace Quillen.FinitePosetInsertion
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  (m : J) (hm : IsMax m)

/-- The unchanged old indexing subposet. -/
abbrev Old := ({m}ᶜ : Set J)

/-- The strict boundary embeds literally into the old subposet. -/
def boundaryInclusion : Set.Iio m ⥤ Old m :=
  (show Monotone (fun x : Set.Iio m ↦ (⟨x.val, ne_of_lt x.property⟩ : Old m)) from
    fun _ _ h ↦ h).functor

include hm in
/-- A predecessor of an old vertex cannot be the removed maximal vertex. -/
theorem predecessor_ne {x y : J} (hxy : x ≤ y) (hy : y ≠ m) : x ≠ m := by
  intro hx
  subst x
  exact hy (hm.eq_of_le hxy).symm

variable (R : Old m ⥤ C) (c : Cocone (boundaryInclusion m ⋙ R))

/-- The one new object is the actual latching cocone point. -/
def insertedObj (x : J) : C := by
  classical
  exact if hx : x = m then c.pt else R.obj ⟨x, hx⟩

/-- Canonical equality identification at an unchanged old object. -/
def insertedOldIso (x : Old m) : insertedObj m R c x.val ≅ R.obj x :=
  eqToIso (by
    have hx : x.val ≠ m := x.property
    simp [insertedObj, hx])

/-- Canonical equality identification at the newly attached object. -/
def insertedNewIso : insertedObj m R c m ≅ c.pt :=
  eqToIso (by simp [insertedObj])

/-- Every new arrow is either an old diagram arrow or an actual boundary leg. -/
def insertedMap {x y : J} (f : x ⟶ y) : insertedObj m R c x ⟶ insertedObj m R c y := by
  classical
  by_cases hy : y = m
  · subst y
    by_cases hx : x = m
    · subst x
      exact 𝟙 _
    · exact (insertedOldIso m R c ⟨x, hx⟩).hom ≫
        c.ι.app ⟨x, lt_of_le_of_ne (leOfHom f) hx⟩ ≫ (insertedNewIso m R c).inv
  · have hx := predecessor_ne m hm (leOfHom f) hy
    exact (insertedOldIso m R c ⟨x, hx⟩).hom ≫
      R.map (homOfLE (show (⟨x, hx⟩ : Old m) ≤ ⟨y, hy⟩ from leOfHom f)) ≫
        (insertedOldIso m R c ⟨y, hy⟩).inv

/-- Insertion respects the original identities. -/
theorem insertedMap_id (x : J) : insertedMap m hm R c (𝟙 x) = 𝟙 (insertedObj m R c x) := by
  classical
  by_cases hx : x = m
  · subst x
    simp [insertedMap]
  · simp [insertedMap, hx]

/-- The full original composition law follows from strict cocone naturality. -/
theorem insertedMap_comp {x y z : J} (f : x ⟶ y) (g : y ⟶ z) :
    insertedMap m hm R c (f ≫ g) = insertedMap m hm R c f ≫ insertedMap m hm R c g := by
  classical
  by_cases hz : z = m
  · subst z
    by_cases hy : y = m
    · subst y
      by_cases hx : x = m
      · subst x; simp [insertedMap]
      · simp [insertedMap, hx]
    · have hx := predecessor_ne m hm (leOfHom f) hy
      simp only [insertedMap, dite_eq_right hx, dite_eq_right hy, dite_true,
        Category.assoc, Iso.inv_hom_id_assoc]
      let bx : Set.Iio m := ⟨x, lt_of_le_of_ne (leOfHom (f ≫ g)) hx⟩
      let by' : Set.Iio m := ⟨y, lt_of_le_of_ne (leOfHom g) hy⟩
      let a : bx ⟶ by' := homOfLE (leOfHom f)
      have ha : (boundaryInclusion m).map a =
          homOfLE (show (⟨x, hx⟩ : Old m) ≤ ⟨y, hy⟩ from leOfHom f) :=
        Subsingleton.elim _ _
      have hc := c.w a
      change R.map ((boundaryInclusion m).map a) ≫ c.ι.app by' = c.ι.app bx at hc
      rw [ha] at hc
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (insertedOldIso m R c ⟨x, hx⟩).hom ≫
          k ≫ (insertedNewIso m R c).inv) hc.symm
  · have hy := predecessor_ne m hm (leOfHom g) hz
    have hx := predecessor_ne m hm (leOfHom f) hy
    simp only [insertedMap, dite_eq_right hx, dite_eq_right hy, dite_eq_right hz,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (R.map _), ← R.map_comp]
    rfl

/-- The complete original poset diagram with its genuinely attached maximal
vertex. No functoriality or commuting-face assertion is assumed. -/
def insertedDiagram : J ⥤ C where
  obj := insertedObj m R c
  map := insertedMap m hm R c
  map_id := insertedMap_id m hm R c
  map_comp := insertedMap_comp m hm R c

@[simp] theorem insertedDiagram_obj_old (x : Old m) :
    (insertedDiagram m hm R c).obj x.val = R.obj x := by
  have hx : x.val ≠ m := x.property
  simp [insertedDiagram, insertedObj, hx]

@[simp] theorem insertedDiagram_obj_new :
    (insertedDiagram m hm R c).obj m = c.pt := by
  simp [insertedDiagram, insertedObj]

/-- Insertion restricts to the original old diagram through the canonical
object equalities, on every old arrow simultaneously. -/
def insertedOldDiagramIso :
    FinitePosetLatching.inclusion (Old m) ⋙ insertedDiagram m hm R c ≅ R :=
  NatIso.ofComponents (fun x ↦ insertedOldIso m R c x) (by
    intro x y f
    have hy : y.val ≠ m := y.property
    change insertedMap m hm R c (homOfLE (show x.val ≤ y.val from leOfHom f)) ≫
      (insertedOldIso m R c y).hom = (insertedOldIso m R c x).hom ≫ R.map f
    simp only [insertedMap, dite_eq_right hy, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    congr 1)

variable (G : J ⥤ C)
  (p : R ⟶ FinitePosetLatching.restriction G (Old m)) (q : c.pt ⟶ G.obj m)

/-- Comparison with the original diagram, retaining every specified old map. -/
def insertedProjectionApp (x : J) : (insertedDiagram m hm R c).obj x ⟶ G.obj x := by
  classical
  by_cases hx : x = m
  · subst x
    exact (insertedNewIso m R c).hom ≫ q
  · exact (insertedOldIso m R c ⟨x, hx⟩).hom ≫ p.app ⟨x, hx⟩

variable (comm : ∀ x : Set.Iio m,
  c.ι.app x ≫ q = p.app ((boundaryInclusion m).obj x) ≫ G.map (homOfLE x.property.le))

/-- Strict agreement on the full lower boundary makes the original comparison
natural on the extended diagram. -/
def insertedProjection : insertedDiagram m hm R c ⟶ G where
  app := insertedProjectionApp m hm R c G p q
  naturality x y f := by
    classical
    change insertedMap m hm R c f ≫ insertedProjectionApp m hm R c G p q y =
      insertedProjectionApp m hm R c G p q x ≫ G.map f
    by_cases hy : y = m
    · subst y
      by_cases hx : x = m
      · subst x
        have hf : f = 𝟙 m := Subsingleton.elim _ _
        subst f
        simp [insertedMap, insertedProjectionApp]
      · simp only [insertedMap, insertedProjectionApp, dite_eq_right hx, dite_true,
          Category.assoc, Iso.inv_hom_id_assoc]
        exact congrArg (fun k ↦ (insertedOldIso m R c ⟨x, hx⟩).hom ≫ k)
          (comm ⟨x, lt_of_le_of_ne (leOfHom f) hx⟩)
    · have hx := predecessor_ne m hm (leOfHom f) hy
      simp only [insertedMap, insertedProjectionApp, dite_eq_right hx, dite_eq_right hy,
        Category.assoc, Iso.inv_hom_id_assoc]
      exact congrArg (fun k ↦ (insertedOldIso m R c ⟨x, hx⟩).hom ≫ k)
        (p.naturality (homOfLE (show (⟨x, hx⟩ : Old m) ≤ ⟨y, hy⟩ from leOfHom f)))

/-- The complete previously specified comparison is preserved on the old
subdiagram; it is not re-chosen independently at its vertices. -/
theorem insertedProjection_restrict :
    Functor.whiskerLeft (FinitePosetLatching.inclusion (Old m))
      (insertedProjection m hm R c G p q comm) =
        (insertedOldDiagramIso m hm R c).hom ≫ p := by
  ext x
  have hx : x.val ≠ m := x.property
  change insertedProjectionApp m hm R c G p q x.val = _
  simp only [insertedProjectionApp, dite_eq_right hx]
  rfl

/-- Weakness is inherited from the specified old comparison and the actual
new projection, with only equality identifications at the unchanged objects. -/
theorem insertedProjection_weak (W : Quillen.Waldhausen.Structure C)
    (hp : ∀ x, W.weq (p.app x)) (hq : W.weq q) (x : J) :
    W.weq ((insertedProjection m hm R c G p q comm).app x) := by
  classical
  by_cases hx : x = m
  · subst x
    change W.weq (insertedProjectionApp m hm R c G p q m)
    simp only [insertedProjectionApp, dite_true]
    exact W.weq.comp_mem _ _ (W.weq_iso _ inferInstance) hq
  · change W.weq (insertedProjectionApp m hm R c G p q x)
    simp only [insertedProjectionApp, dite_eq_right hx]
    exact W.weq.comp_mem _ _ (W.weq_iso _ inferInstance) (hp ⟨x, hx⟩)

/-- A comparison on the old diagram gives the actual boundary cocone in the
original new target vertex. -/
def comparisonBoundaryCocone : Cocone (boundaryInclusion m ⋙ R) where
  pt := G.obj m
  ι := {
    app x := p.app ((boundaryInclusion m).obj x) ≫ G.map (homOfLE x.property.le)
    naturality x y f := by
      change R.map ((boundaryInclusion m).map f) ≫
        (p.app ((boundaryInclusion m).obj y) ≫ G.map (homOfLE y.property.le)) =
        (p.app ((boundaryInclusion m).obj x) ≫ G.map (homOfLE x.property.le)) ≫ 𝟙 (G.obj m)
      rw [Category.comp_id, ← Category.assoc, p.naturality, Category.assoc]
      change p.app ((boundaryInclusion m).obj x) ≫
        (G.map _ ≫ G.map _) = _
      rw [← G.map_comp]
      rfl }

end Quillen.FinitePosetInsertion
