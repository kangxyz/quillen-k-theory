import Quillen.Topology.Realization.Classification
import Quillen.Topology.Realization.HomotopyBridge
import Mathlib.Topology.Homotopy.Equiv

/-! # Explicit contraction of classification grids onto the ordinary nerve -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u v

namespace Quillen.Classification
variable {D : Type u} [Category.{v} D] {n : SimplexCategory}

/-- A grid arrow commutes with the maps out of the initial row. -/
theorem zeroRow_naturality (F : Grid n ⥤ D) {p q : Grid n} (f : p ⟶ q) :
    verticalMap F 0 p.1 p.2 (Fin.zero_le _) ≫ F.map f =
      F.map (homOfLE (show ((0, p.2) : Grid n) ≤ (0, q.2) from
        ⟨le_rfl, (leOfHom f).2⟩)) ≫ verticalMap F 0 q.1 q.2 (Fin.zero_le _) := by
  simp only [verticalMap, ← F.map_comp]
  congr 1

/-- Transporting a rectangle to any other ordered pair of rows recovers its
actual diagram arrow. This includes the diagonal rectangle. -/
theorem transport_conjugation (F : Grid n ⥤ D) (hF : IsVerticalIso F)
    {p q : Grid n} (f : p ⟶ q) (s t : Fin (n.len + 1)) (hst : s ≤ t) :
    (transport F hF p.1 s p.2).inv ≫ F.map f ≫
      (transport F hF q.1 t q.2).hom =
      F.map (homOfLE (show ((s, p.2) : Grid n) ≤ (t, q.2) from
        ⟨hst, (leOfHom f).2⟩)) := by
  haveI : IsIso (verticalMap F 0 p.1 p.2 (Fin.zero_le _)) := hF _ _ _ (Fin.zero_le _)
  haveI : IsIso (verticalMap F 0 q.1 q.2 (Fin.zero_le _)) := hF _ _ _ (Fin.zero_le _)
  haveI : IsIso (verticalMap F 0 s p.2 (Fin.zero_le _)) := hF _ _ _ (Fin.zero_le _)
  haveI : IsIso (verticalMap F 0 t q.2 (Fin.zero_le _)) := hF _ _ _ (Fin.zero_le _)
  change (inv (verticalMap F 0 s p.2 (Fin.zero_le _)) ≫ verticalMap F 0 p.1 p.2 (Fin.zero_le _)) ≫
    F.map f ≫ (inv (verticalMap F 0 q.1 q.2 (Fin.zero_le _)) ≫ verticalMap F 0 t q.2 (Fin.zero_le _)) = _
  apply (cancel_epi (verticalMap F 0 s p.2 (Fin.zero_le _))).mp
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, zeroRow_naturality F f]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact (zeroRow_naturality F (p := (s, p.2)) (q := (t, q.2))
    (homOfLE ⟨hst, (leOfHom f).2⟩)).symm

/-- Move each grid object to an arbitrary row and conjugate every arrow by
its coherent vertical isomorphism. -/
def moveRows (F : Grid n ⥤ D) (hF : IsVerticalIso F)
    (r : Grid n → Fin (n.len + 1)) : Grid n ⥤ D where
  obj p := F.obj (r p, p.2)
  map {p q} f := (transport F hF p.1 (r p) p.2).inv ≫ F.map f ≫
    (transport F hF q.1 (r q) q.2).hom
  map_id p := by
    rcases p with ⟨s, i⟩
    simp
  map_comp f g := by
    rw [F.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The moved grid still has invertible vertical arrows. -/
theorem moveRows_isVerticalIso (F : Grid n ⥤ D) (hF : IsVerticalIso F)
    (r : Grid n → Fin (n.len + 1)) : IsVerticalIso (moveRows F hF r) := by
  intro s t i hst
  haveI := hF s t i hst
  dsimp [moveRows]
  infer_instance

@[simp]
theorem moveRows_first (F : Grid n ⥤ D) (hF : IsVerticalIso F) :
    moveRows F hF (fun p ↦ p.1) = F := by
  refine CategoryTheory.Functor.ext (F := moveRows F hF (fun p ↦ p.1)) (G := F)
    (fun p ↦ by cases p; rfl) ?_
  intro p q f
  rcases p with ⟨s, i⟩
  rcases q with ⟨t, j⟩
  simp [moveRows]

@[simp]
theorem moveRows_second (F : Grid n ⥤ D) (hF : IsVerticalIso F) :
    moveRows F hF (fun p ↦ p.2) = second n ⋙ diagonal n ⋙ F := by
  refine CategoryTheory.Functor.ext (F := moveRows F hF (fun p ↦ p.2))
    (G := second n ⋙ diagonal n ⋙ F) (fun p ↦ rfl) ?_
  intro p q f
  change _ = 𝟙 _ ≫ F.map ((diagonal n).map ((second n).map f)) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact (transport_conjugation F hF f p.2 q.2 (leOfHom f).2).trans
    (congrArg F.map (Subsingleton.elim _ _))

/-- The interval simplex chooses the old row or the diagonal row. -/
def cutRows (ψ : Fin (n.len + 1) → Fin 2) (p : Grid n) : Fin (n.len + 1) :=
  if ψ p.1 = 0 then p.1 else p.2

def cylinderSimplex (F : Grid n ⥤ D) (hF : IsVerticalIso F)
    (ψ : Fin (n.len + 1) → Fin 2) : Grid n ⥤ D :=
  moveRows F hF (cutRows ψ)


/-- Inverse transport is also strictly compatible with simplex reindexing. -/
theorem transport_precomp_inv {m : SimplexCategory} (F : Grid n ⥤ D)
    (hF : IsVerticalIso F) (α : m ⟶ n) (s t i : Fin (m.len + 1)) :
    (transport (gridMap α ⋙ F) (hF.precomp α) s t i).inv =
      (transport F hF (α.toOrderHom s) (α.toOrderHom t) (α.toOrderHom i)).inv :=
  congrArg Iso.inv (Iso.ext (transport_precomp F hF α s t i))

@[simp]
theorem gridMap_obj {m n : SimplexCategory} (α : m ⟶ n) (p : Grid m) :
    (gridMap α).obj p = (α.toOrderHom p.1, α.toOrderHom p.2) := rfl

/-- Heterogeneous form of reindexing, allowing the new row indices to be
identified by arbitrary proved equalities. -/
theorem moveRows_precomp_map {m : SimplexCategory} (F : Grid n ⥤ D)
    (hF : IsVerticalIso F) (α : m ⟶ n) {p q : Grid m} (f : p ⟶ q)
    (s t : Fin (m.len + 1)) (s' t' : Fin (n.len + 1))
    (hs : α.toOrderHom s = s') (ht : α.toOrderHom t = t') :
    HEq ((transport (gridMap α ⋙ F) (hF.precomp α) p.1 s p.2).inv ≫
      F.map ((gridMap α).map f) ≫
      (transport (gridMap α ⋙ F) (hF.precomp α) q.1 t q.2).hom)
      ((transport F hF (α.toOrderHom p.1) s' (α.toOrderHom p.2)).inv ≫
      F.map ((gridMap α).map f) ≫
      (transport F hF (α.toOrderHom q.1) t' (α.toOrderHom q.2)).hom) := by
  subst s'
  subst t'
  apply heq_of_eq
  rw [transport_precomp, transport_precomp_inv]

/-- The coherent conjugation is natural for every face and degeneracy. -/
theorem cylinderSimplex_precomp {m : SimplexCategory} (F : Grid n ⥤ D)
    (hF : IsVerticalIso F) (α : m ⟶ n) (ψ : Fin (n.len + 1) → Fin 2) :
    cylinderSimplex (gridMap α ⋙ F) (hF.precomp α) (ψ ∘ α.toOrderHom) =
      gridMap α ⋙ cylinderSimplex F hF ψ := by
  apply CategoryTheory.Functor.hext
  · intro p
    rcases p with ⟨s, i⟩
    dsimp [cylinderSimplex, moveRows, cutRows, gridMap]
    split_ifs <;> rfl
  · intro p q f
    exact moveRows_precomp_map F hF α f
      (cutRows (ψ ∘ α.toOrderHom) p) (cutRows (ψ ∘ α.toOrderHom) q)
      (cutRows ψ ((gridMap α).obj p)) (cutRows ψ ((gridMap α).obj q))
      (by dsimp [cutRows, gridMap]; split_ifs <;> rfl)
      (by dsimp [cutRows, gridMap]; split_ifs <;> rfl)

/-- An explicit simplicial cylinder, through vertical isomorphisms. -/
def cylinder (D : Type u) [Category.{v} D] : sSet D ⊗ Δ[1] ⟶ sSet D where
  app n := ↾fun z ↦ ⟨cylinderSimplex z.1.1 z.1.2 z.2.down.toOrderHom,
    moveRows_isVerticalIso z.1.1 z.1.2 _⟩
  naturality n m α := by
    ext z
    apply Subtype.ext
    exact cylinderSimplex_precomp z.1.1 z.1.2 α.unop z.2.down.toOrderHom

@[simp]
theorem cylinder_zero (D : Type u) [Category.{v} D] :
    SSet.ι₀ ≫ cylinder D = 𝟙 (sSet D) := by
  ext n F
  apply Subtype.ext
  change cylinderSimplex F.1 F.2 (fun _ ↦ 0) = F.1
  have hc : cutRows (n := n.unop) (fun _ ↦ (0 : Fin 2)) = fun p ↦ p.1 := by
    funext p
    exact if_pos rfl
  rw [cylinderSimplex, hc]
  exact moveRows_first F.1 F.2

@[simp]
theorem cylinder_one (D : Type u) [Category.{v} D] :
    SSet.ι₁ ≫ cylinder D = evaluation D ≫ constant D := by
  ext n F
  apply Subtype.ext
  change cylinderSimplex F.1 F.2 (fun _ ↦ 1) = second n.unop ⋙ diagonal n.unop ⋙ F.1
  have hc : cutRows (n := n.unop) (fun _ ↦ (1 : Fin 2)) = fun p ↦ p.2 := by
    funext p
    exact if_neg (by change (1 : Fin 2) ≠ 0; decide)
  rw [cylinderSimplex, hc]
  exact moveRows_second F.1 F.2

/-- The classification diagonal retracts onto the ordinary nerve by a genuine
simplicial homotopy, with the prescribed diagonal evaluation map. -/
def homotopy (D : Type u) [Category.{v} D] :
    SSet.Homotopy (𝟙 (sSet D)) (evaluation D ≫ constant D) where
  h := cylinder D
  h₀ := cylinder_zero D
  h₁ := cylinder_one D
  rel := by ext n z; exact z.1.property.elim

/-- The classification diagonal and the ordinary nerve have the same actual
realization homotopy type. Its forward map is diagonal evaluation. -/
def realizationHomotopyEquiv (D : Type u) [Category.{v} D] :
    ContinuousMap.HomotopyEquiv |sSet D| |nerve D| where
  toFun := (SSet.toTop.map (evaluation D)).hom
  invFun := (SSet.toTop.map (constant D)).hom
  left_inv := by
    have h := (realizationSimplicialHomotopy (homotopy D)).symm
    exact ⟨by simpa only [SSet.toTop.map_id, SSet.toTop.map_comp,
      TopCat.hom_id, TopCat.hom_comp] using h⟩
  right_inv := by
    have h := congrArg (fun f ↦ (SSet.toTop.map f).hom) (constant_evaluation D)
    have he : (SSet.toTop.map (evaluation D)).hom.comp
        (SSet.toTop.map (constant D)).hom = ContinuousMap.id _ := by
      simpa only [SSet.toTop.map_comp, SSet.toTop.map_id, TopCat.hom_comp, TopCat.hom_id] using h
    rw [he]

@[simp]
theorem realizationHomotopyEquiv_toFun (D : Type u) [Category.{v} D] :
    (realizationHomotopyEquiv D).toFun = (SSet.toTop.map (evaluation D)).hom := rfl


/-- Transport in a vertically constant diagram is the identity. -/
@[simp]
theorem transport_constant (F : Fin (n.len + 1) ⥤ D)
    (hF : IsVerticalIso (second n ⋙ F)) (s t i : Fin (n.len + 1)) :
    transport (second n ⋙ F) hF s t i = Iso.refl (F.obj i) := by
  apply Iso.ext
  change inv (F.map (𝟙 i)) ≫ F.map (𝟙 i) = 𝟙 _
  simp

/-- The deformation fixes every diagram already constant vertically. -/
@[simp]
theorem moveRows_constant (F : Fin (n.len + 1) ⥤ D)
    (hF : IsVerticalIso (second n ⋙ F)) (r : Grid n → Fin (n.len + 1)) :
    moveRows (second n ⋙ F) hF r = second n ⋙ F := by
  refine CategoryTheory.Functor.ext (fun p ↦ rfl) ?_
  intro p q f
  rcases p with ⟨s, i⟩
  rcases q with ⟨t, j⟩
  simp only [moveRows, transport_constant, Iso.refl_inv, Iso.refl_hom,
    Functor.comp_map, eqToHom_refl]
  rfl

/-- The simplicial deformation is relative to the entire constant-nerve image. -/
@[simp]
theorem constant_cylinder (D : Type u) [Category.{v} D] :
    (constant D ▷ Δ[1]) ≫ cylinder D = fst (nerve D) Δ[1] ≫ constant D := by
  ext n z
  apply Subtype.ext
  change moveRows (second n.unop ⋙ z.1) _ _ = second n.unop ⋙ z.1
  exact moveRows_constant z.1 _ _

/-- In particular, the actual topological homotopy fixes every chosen
vertex in the constant-nerve image. -/
theorem realizationHomotopy_fixed_vertex (D : Type u) [Category.{v} D]
    (x : (nerve D) _⦋0⦌) (t : unitInterval) :
    realizationSimplicialHomotopy (homotopy D)
      (t, realizationPoint ((constant D).app _ x)) =
        realizationPoint ((constant D).app _ x) := by
  apply realizationSimplicialHomotopy_fixed_vertex (homotopy D)
    ((constant D).app _ x) ((constant D).app _ x) _ t
  change SSet.yonedaEquiv.symm ((constant D).app _ x) ▷ Δ[1] ≫ cylinder D = _
  rw [← SSet.yonedaEquiv_symm_comp]
  rw [comp_whiskerRight, Category.assoc, constant_cylinder,
    ← Category.assoc, whiskerRight_fst, Category.assoc]

end Quillen.Classification
