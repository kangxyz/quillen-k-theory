import Quillen.Waldhausen.SConstruction.Rows.PointwisePushouts
import Quillen.Waldhausen.SConstruction.Rows.Basic
import Quillen.Waldhausen.SConstruction.Rows.RelativePushout
import Quillen.Waldhausen.SConstruction.Rows.Pushouts
import Quillen.Waldhausen.SConstruction.Rows.Structure
import Quillen.Waldhausen.SConstruction.Rows.Reindex
import Quillen.Waldhausen.SConstruction.Rows.GridBridge
import Quillen.Waldhausen.ArrowCategory.Structure
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.SConstruction.Rows.PointwisePushouts, `Quillen.Waldhausen.SConstruction.Rows.Basic, `Quillen.Waldhausen.SConstruction.Rows.RelativePushout, `Quillen.Waldhausen.SConstruction.Rows.Pushouts, `Quillen.Waldhausen.SConstruction.Rows.Structure, `Quillen.Waldhausen.SConstruction.Rows.Reindex, `Quillen.Waldhausen.SConstruction.Rows.GridBridge, `Quillen.Waldhausen.ArrowCategory.Structure]
  let mut count : Nat := 0
  for origin in targets do
    let mut subtotal : Nat := 0
    for (name, _) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      unless env.header.moduleNames[index.toNat]! == origin do continue
      count := count + 1
      subtotal := subtotal + 1
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{origin}: {name} depends on unsupported assumption {dependency}"
      logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
    logInfo m!"ORIGIN_COUNT {origin}: {subtotal}"
  unless count == 96 do throwError "Expected 96 quotient-row/pointwise-arrow origins, got {count}"
  logInfo m!"Audited all {count} quotient-row/pointwise-arrow declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C) {n : SimplexCategory}

-- No restriction is placed on natural transformations in the full row category.
example {F G : Obj W n} (η : F.obj ⟶ G.obj) :
    ((objects W n).homMk η : F ⟶ G).hom = η := rfl
example {F G : Obj W n} (η : F ⟶ G) :
    (waldhausenStructure W n).weq η ↔ ∀ p, W.weq (η.hom.app p) := Iff.rfl
example {F G : Obj W n} (η : F ⟶ G) :
    (waldhausenStructure W n).cof η ↔
      ∀ i j k hij hjk, ExtensionCategory.cof W ((horizontalArrow W i j k hij hjk).map η) := Iff.rfl
example {F G : Obj W n} {η : F ⟶ G} (hη : (waldhausenStructure W n).cof η)
    (p : Interval n) : W.cof (η.hom.app p) := cof_app W hη p
example {F G : Obj W n} {η : F ⟶ G} (hη : (waldhausenStructure W n).cof η)
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    W.cof (ExtensionCategory.relativeMap W ((horizontalArrow W i j k hij hjk).map η)) :=
  (hη i j k hij hjk).2
example (p : Interval n) : IsExact (waldhausenStructure W n).cof (waldhausenStructure W n).weq
    W.cof W.weq (evaluation W p) := evaluation_exact W p
example (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    IsExact (waldhausenStructure W n).cof (waldhausenStructure W n).weq
      (ExtensionCategory.waldhausenStructure W).cof (ExtensionCategory.waldhausenStructure W).weq
      (horizontalArrow W i j k hij hjk) := horizontalArrow_exact W i j k hij hjk
example {A B D : Obj W n} {P : Interval n ⥤ C}
    (f : A ⟶ B) (g : A ⟶ D) (i : B.obj ⟶ P) (j : D.obj ⟶ P)
    (hf : (waldhausenStructure W n).cof f)
    (hp : ∀ p, IsPushout (f.hom.app p) (g.hom.app p) (i.app p) (j.app p)) : IsRow W P :=
  isRow_of_pointwise_pushout W f g i j hf hp
example {A B D P : Obj W n} {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ P} {j : D ⟶ P}
    (hf : (waldhausenStructure W n).cof f) (h : IsPushout f g i j) (p : Interval n) :
    IsPushout (f.hom.app p) (g.hom.app p) (i.hom.app p) (j.hom.app p) :=
  pointwise_of_isPushout W hf h p
example {A B D : Obj W n} (f : A ⟶ B) (g : A ⟶ D) (hf : (waldhausenStructure W n).cof f) :
    ∃ (P : Obj W n) (i : B ⟶ P) (j : D ⟶ P), IsPushout f g i j ∧
      (∀ p, IsPushout (f.hom.app p) (g.hom.app p) (i.hom.app p) (j.hom.app p)) ∧
      (waldhausenStructure W n).cof j := exists_row_pushout W f g hf
example : (waldhausenStructure W n).zero.obj = (Functor.const (Interval n)).obj W.zero := rfl
example {m : SimplexCategory} (α : m ⟶ n) :
    IsExact (waldhausenStructure W n).cof (waldhausenStructure W n).weq
      (waldhausenStructure W m).cof (waldhausenStructure W m).weq (reindex W α) := reindex_exact W α
example {m : SimplexCategory} (α : m ⟶ n) (F : Obj W n) :
    ((reindex W α).obj F).obj = indexMap α ⋙ F.obj := rfl
example {m : SimplexCategory} (α : m ⟶ n) {F G : Obj W n} (η : F ⟶ G) (p : Interval m) :
    ((reindex W α).map η).hom.app p = η.hom.app ((indexMap α).obj p) := rfl
example {m : SimplexCategory} (α : m ⟶ n) :
    (reindex W α).obj (waldhausenStructure W n).zero = (waldhausenStructure W m).zero := reindex_zero W α
example : reindex W (𝟙 n) = 𝟭 (Obj W n) := reindex_id W n
example {l m : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n) :
    reindex W (α ≫ β) = reindex W β ⋙ reindex W α := reindex_comp W α β
example {m : SimplexCategory} (F : Grid₂ n m ⥤ C) :
    IsSimplex₂ W.cof W.weq F ↔
      (∀ t : Fin (m.len + 1), IsRow W (gridRestriction t ⋙ F)) ∧
      (∀ (s t : Fin (m.len + 1)) (i j : Fin (n.len + 1)) (hst : s ≤ t) (hij : i ≤ j),
        W.weq (F.map (homOfLE (show grid₂ s i j hij ≤ grid₂ t i j hij from
          ⟨hst, le_rfl, le_rfl⟩)))) := isSimplex₂_iff W F
example {n' m' m : SimplexCategory} (α : n' ⟶ n) (β : m' ⟶ m) (t : Fin (m'.len + 1)) :
    gridRestriction t ⋙ gridMap₂ α β = indexMap α ⋙ gridRestriction (β.toOrderHom t) :=
  gridRestriction_reindex α β t
end Quillen.Waldhausen.QuotientRows
namespace Quillen.Waldhausen.ArrowCategory
variable {C : Type u} [Category.{v} C] (W : Structure C)
example {X Y : Arrow C} (η : X ⟶ Y) :
    (waldhausenStructure W).cof η ↔ W.cof η.left ∧ W.cof η.right := Iff.rfl
example {X Y : Arrow C} (η : X ⟶ Y) :
    (waldhausenStructure W).weq η ↔ W.weq η.left ∧ W.weq η.right := Iff.rfl
example : (waldhausenStructure W).zero = Arrow.mk (𝟙 W.zero) := rfl
example : IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq
    W.cof W.weq (Arrow.leftFunc : Arrow C ⥤ C) := source_exact W
example : IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq
    W.cof W.weq (Arrow.rightFunc : Arrow C ⥤ C) := target_exact W
example {A B D P : Arrow C} {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ P} {j : D ⟶ P}
    (hf : (waldhausenStructure W).cof f) (h : IsPushout f g i j) :
    IsPushout f.left g.left i.left j.left ∧ IsPushout f.right g.right i.right j.right :=
  pointwise_of_isPushout W hf h
end Quillen.Waldhausen.ArrowCategory
