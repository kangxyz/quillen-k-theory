import Quillen.Waldhausen.Fibration.MixedNerves.RowPostcompose
import Quillen.Waldhausen.Fibration.TrivialCofibrations.Category
import Quillen.Waldhausen.SConstruction.Rows.NervePresentation

/-! # The actual coarse row presentation on unchanged quotient diagrams

The fine and coarse row object conditions agree because the cofibrations
agree and the zero/pushout conditions are absolute. The explicit functors
change only those proofs and retain every original diagram and natural
transformation. They restrict to the actual coarse weak maps and commute
with every original row restriction.
-/
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.MixedNerves
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- Actual row object conditions are insensitive to the change of weak class. -/
theorem isRow_coarse_iff {n : SimplexCategory} (F : Interval n ⥤ C) :
    QuotientRows.IsRow V F ↔ QuotientRows.IsRow N.coarse F := by
  constructor
  · intro h
    exact ⟨h.zero, fun i j k hij hjk ↦ by rw [N.cof_eq]; exact h.cofibration i j k hij hjk,
      h.quotient⟩
  · intro h
    exact ⟨h.zero, fun i j k hij hjk ↦ by rw [← N.cof_eq]; exact h.cofibration i j k hij hjk,
      h.quotient⟩

/-- View an unchanged original fine row as a genuine coarse row. -/
def coarseRowView (n : SimplexCategory) : QuotientRows.Obj V n ⥤ QuotientRows.Obj N.coarse n where
  obj X := ⟨X.obj, (isRow_coarse_iff N X.obj).1 X.property⟩
  map f := (QuotientRows.objects N.coarse n).homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl
/-- The inverse view retains the same original quotient diagram. -/
def fineRowView (n : SimplexCategory) : QuotientRows.Obj N.coarse n ⥤ QuotientRows.Obj V n where
  obj X := ⟨X.obj, (isRow_coarse_iff N X.obj).2 X.property⟩
  map f := (QuotientRows.objects V n).homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem coarseRowView_fineRowView (n : SimplexCategory) :
    coarseRowView N n ⋙ fineRowView N n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem fineRowView_coarseRowView (n : SimplexCategory) :
    fineRowView N n ⋙ coarseRowView N n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Coarse weak maps on the actual unchanged fine quotient-row object type. -/
abbrev coarseWeakRows (n : SimplexCategory) :=
  TrivialCofibrations.WeakCategory (RowWeakEquivalences.coarseStructure N n).weq

/-- Literal original row restriction, packaged by the same compatible base functor. -/
def coarseWeakRowsReindex {m n : SimplexCategory} (α : m ⟶ n) :
    coarseWeakRows N n ⥤ coarseWeakRows N m :=
  widePostcompose (rowReindexCompatible N α).toFunctor _ _ (rowReindexCompatible N α).coarse

/-- The coarse weak maps are the same original components in the standard coarse row model. -/
def coarseWeakRowsToStandard (n : SimplexCategory) : coarseWeakRows N n ⥤ QuotientRows.WeakRows N.coarse n :=
  widePostcompose (coarseRowView N n) _ _ (fun _ h ↦ h)
/-- The inverse keeps every original coarse weak component unchanged. -/
def standardToCoarseWeakRows (n : SimplexCategory) : QuotientRows.WeakRows N.coarse n ⥤ coarseWeakRows N n :=
  widePostcompose (fineRowView N n) _ _ (fun _ h ↦ h)

@[simp] theorem coarseWeakRowsToStandard_inverse (n : SimplexCategory) :
    coarseWeakRowsToStandard N n ⋙ standardToCoarseWeakRows N n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem standardToCoarseWeakRows_inverse (n : SimplexCategory) :
    standardToCoarseWeakRows N n ⋙ coarseWeakRowsToStandard N n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Genuine categorical equivalence, proved by the literal inverse views. -/
def coarseWeakRowsEquivalence (n : SimplexCategory) :
    coarseWeakRows N n ≌ QuotientRows.WeakRows N.coarse n :=
  CategoryTheory.Equivalence.mk (coarseWeakRowsToStandard N n) (standardToCoarseWeakRows N n)
    (eqToIso (coarseWeakRowsToStandard_inverse N n).symm)
    (eqToIso (standardToCoarseWeakRows_inverse N n))

@[simp] theorem coarseWeakRowsToStandard_obj (n : SimplexCategory) (X : coarseWeakRows N n) :
    ((coarseWeakRowsToStandard N n).obj X).obj.obj = X.obj.obj := rfl
@[simp] theorem coarseWeakRowsToStandard_map (n : SimplexCategory)
    {X Y : coarseWeakRows N n} (f : X ⟶ Y) :
    ((coarseWeakRowsToStandard N n).map f).hom.hom = f.hom.hom := rfl

/-- The actual coarse restriction commutes strictly with the original row view. -/
theorem coarseWeakRowsToStandard_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    coarseWeakRowsReindex N α ⋙ coarseWeakRowsToStandard N m =
      coarseWeakRowsToStandard N n ⋙ QuotientRows.weakRowsReindex N.coarse α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- The actual inverse has the same strict original restriction formula. -/
theorem standardToCoarseWeakRows_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    QuotientRows.weakRowsReindex N.coarse α ⋙ standardToCoarseWeakRows N m =
      standardToCoarseWeakRows N n ⋙ coarseWeakRowsReindex N α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual coarse weak row categories with the original ordinal restriction. -/
def coarseWeakRowCategories : SimplexCategoryᵒᵖ ⥤ Cat.{v,max u v} where
  obj n := Cat.of (coarseWeakRows N n.unop)
  map α := Cat.Hom.ofFunctor (coarseWeakRowsReindex N α.unop)
  map_id _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp _ _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Nerve of the actual coarse weak maps on unchanged original fine row objects. -/
def coarseWeakRowNerve : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := coarseWeakRowCategories N ⋙ nerveFunctor

/-- Exact bisimplicial identification with the standard coarse weak row nerve. -/
def coarseWeakRowNerveIso : coarseWeakRowNerve N ≅ QuotientRows.weakRowNerve N.coarse where
  hom := {
    app n := nerveMap (coarseWeakRowsToStandard N n.unop)
    naturality _ _ _ := by ext k F : 4; apply CategoryTheory.Functor.ext (fun _ ↦ rfl) }
  inv := {
    app n := nerveMap (standardToCoarseWeakRows N n.unop)
    naturality _ _ _ := by ext k F : 4; apply CategoryTheory.Functor.ext (fun _ ↦ rfl) }
  hom_inv_id := by ext n k F : 5; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  inv_hom_id := by ext n k F : 5; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem coarseWeakRowNerveIso_hom_app (n k : SimplexCategory)
    (F : ComposableArrows (coarseWeakRows N n) k.len) :
    ((coarseWeakRowNerveIso N).hom.app (op n)).app (op k) F =
      F ⋙ coarseWeakRowsToStandard N n := rfl

/-- The original diagonal coarse weak-row model is the actual coarse S-construction. -/
def coarseSSetIso : TheoremA.diagonalSSet (coarseWeakRowNerve N) ≅ sSet N.coarse.cof N.coarse.weq :=
  TheoremA.diagonalFunctor.mapIso (coarseWeakRowNerveIso N) ≪≫
    (QuotientRows.sSetWeakRowDiagonalIso N.coarse).symm

/-- The forward map reconstructs the original grid from its unchanged coarse weak chain. -/
@[simp] theorem coarseSSetIso_hom_val (n : SimplexCategory)
    (F : ComposableArrows (coarseWeakRows N n) n.len) :
    ((coarseSSetIso N).hom.app (op n) F).val =
      QuotientRows.weakChainToGrid N.coarse (F ⋙ coarseWeakRowsToStandard N n) := rfl

/-- Every forward grid object is literally the original row object at the original indices. -/
@[simp] theorem coarseSSetIso_hom_obj (n : SimplexCategory)
    (F : ComposableArrows (coarseWeakRows N n) n.len) (t : Fin (n.len+1)) (p : Interval n) :
    (((coarseSSetIso N).hom.app (op n) F).val.obj (t,p)) = (F.obj t).obj.obj.obj p := rfl

end Quillen.Waldhausen.Fibration.MixedNerves
