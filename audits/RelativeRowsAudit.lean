import Quillen.Waldhausen.SConstruction.Rows.PostcomposeDetection
import Quillen.Waldhausen.Fibration.RelativeRows.Index
import Quillen.Waldhausen.Fibration.RelativeRows.Structure
import Quillen.Waldhausen.Fibration.RelativeRows.Reindex
import Quillen.Waldhausen.Fibration.RelativeRows.Tail
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.SConstruction.Rows.PostcomposeDetection, `Quillen.Waldhausen.Fibration.RelativeRows.Index, `Quillen.Waldhausen.Fibration.RelativeRows.Structure, `Quillen.Waldhausen.Fibration.RelativeRows.Reindex, `Quillen.Waldhausen.Fibration.RelativeRows.Tail]
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
  unless count == 76 do throwError "Expected 76 relative-row origins, got {count}"
  logInfo m!"Audited all {count} actual-relative-row declaration origins."
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
  (n : SimplexCategory)
example : addInitial.obj n = ⦋n.len + 1⦌ := rfl
example {m : SimplexCategory} (α : m ⟶ n) : (addInitial.map α).toOrderHom 0 = 0 := rfl
example {m : SimplexCategory} (α : m ⟶ n) (i : Fin (m.len + 1)) :
    (addInitial.map α).toOrderHom i.succ = (α.toOrderHom i).succ := rfl
example {X Y : Obj N n} (η : X.obj.obj ⟶ Y.obj.obj) :
    (((objects N n).homMk ((QuotientRows.objects V (addInitial.obj n)).homMk η) : X ⟶ Y).hom).hom = η := rfl
example (X : Obj N n) (p : Interval n) :
    Acyclic N.coarse (X.obj.obj.obj ((QuotientRows.indexMap (tail.app n)).obj p)) := X.property p
example {X Y : Obj N n} (f : X ⟶ Y) :
    (waldhausenStructure N n).cof f ↔ QuotientRows.cof V (addInitial.obj n) f.hom := Iff.rfl
example {X Y : Obj N n} (f : X ⟶ Y) :
    (waldhausenStructure N n).weq f ↔ ∀ p, V.weq (f.hom.hom.app p) := Iff.rfl
example : (waldhausenStructure N n).zero.obj = QuotientRows.zero V (addInitial.obj n) := rfl
example : IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
    (QuotientRows.waldhausenStructure V (addInitial.obj n)).cof
    (QuotientRows.waldhausenStructure V (addInitial.obj n)).weq (forget N n) := forget_exact N n
example {A B D P : Obj N n} {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ P} {j : D ⟶ P}
    (hf : (waldhausenStructure N n).cof f) (h : IsPushout f g i j) :
    IsPushout f.hom g.hom i.hom j.hom := forget_map_pushout N hf h
example {A B D : Obj N n} (f : A ⟶ B) (g : A ⟶ D) (hf : (waldhausenStructure N n).cof f) :
    ∃ (P : Obj N n) (i : B ⟶ P) (j : D ⟶ P), IsPushout f g i j ∧
      IsPushout f.hom g.hom i.hom j.hom := exists_pushout N f g hf
example {m : SimplexCategory} (α : m ⟶ n) (F : Obj N n) :
    ((reindex N α).obj F).obj.obj = QuotientRows.indexMap (addInitial.map α) ⋙ F.obj.obj := rfl
example {m : SimplexCategory} (α : m ⟶ n) :
    IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
      (waldhausenStructure N m).cof (waldhausenStructure N m).weq (reindex N α) := reindex_exact N α
example : reindex N (𝟙 n) = 𝟭 (Obj N n) := reindex_id N n
example {l m : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n) :
    reindex N (α ≫ β) = reindex N β ⋙ reindex N α := reindex_comp N α β
example {m : SimplexCategory} (α : m ⟶ n) :
    (reindex N α).obj (zero N n) = zero N m := reindex_zero N α
example : IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
    V.cof V.weq (first N n) := first_exact N n
example (X : Obj N n) : (first N n).obj X = X.obj.obj.obj (firstInterval n) := rfl
example {X Y : Obj N n} (f : X ⟶ Y) : (first N n).map f = f.hom.hom.app (firstInterval n) := rfl
example : IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
    (QuotientRows.waldhausenStructure (acyclicStructure N) n).cof
    (QuotientRows.waldhausenStructure (acyclicStructure N) n).weq (tailFunctor N n) := tailFunctor_exact N n
example (X : Obj N n) (p : Interval n) :
    (((tailFunctor N n).obj X).obj.obj p).obj =
      X.obj.obj.obj ((QuotientRows.indexMap (tail.app n)).obj p) := rfl
example {X Y : Obj N n} (f : X ⟶ Y) (p : Interval n) :
    (((tailFunctor N n).map f).hom.app p).hom =
      f.hom.hom.app ((QuotientRows.indexMap (tail.app n)).obj p) := rfl
example : (tailFunctor N n).obj (zero N n) = QuotientRows.zero (acyclicStructure N) n := tailFunctor_zero N n
example {m : SimplexCategory} (α : m ⟶ n) :
    reindex N α ⋙ tailFunctor N m = tailFunctor N n ⋙ QuotientRows.reindex (acyclicStructure N) α :=
  tailFunctor_reindex N α
example : firstTail N n ⋙ CategoryTheory.Prod.snd _ _ = tailFunctor N n := firstTail_snd N n
example : firstTail N n ⋙ CategoryTheory.Prod.fst _ _ = first N n := firstTail_fst N n
example : IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
    (ExtensionCategory.productStructure V (QuotientRows.waldhausenStructure (acyclicStructure N) n)).cof
    (ExtensionCategory.productStructure V (QuotientRows.waldhausenStructure (acyclicStructure N) n)).weq
    (firstTail N n) := firstTail_exact N n
end Quillen.Waldhausen.Fibration.RelativeRows
