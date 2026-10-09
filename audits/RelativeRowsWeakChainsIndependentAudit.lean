import Quillen.Waldhausen.Fibration.RelativeRows.WeakChains
import Quillen.Waldhausen.Fibration.RelativeRows.FiltrationWeakMaps
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.WeakChains, `Quillen.Waldhausen.Fibration.RelativeRows.FiltrationWeakMaps]
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
  unless count == 22 do throwError "Expected 22 relative-weak-chain origins, got {count}"
  logInfo m!"Audited all {count} relative-weak-chain declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse)
example (n : SimplexCategory) (i : Fin (n.len+1)) :
    (initialFiltrationIndex n).obj i = interval 0 i.succ (Fin.zero_le _) := rfl
example {n : SimplexCategory} (F : QuotientRows.Obj V (addInitial.obj n))
    (i : Fin (n.len+1)) : (initialFiltration F).obj i =
      F.obj.obj (interval 0 i.succ (Fin.zero_le _)) := rfl
example {n : SimplexCategory} (F : QuotientRows.Obj V (addInitial.obj n))
    {i j : Fin (n.len+1)} (f : i ⟶ j) : V.cof ((initialFiltration F).map f) := initialFiltration_map_cof F f
example {n : SimplexCategory} (F : QuotientRows.Obj V (addInitial.obj n)) :
    objects N n F ↔ ∀ i j (f : i ⟶ j), N.coarse.weq ((initialFiltration F).map f) :=
  objects_iff_initialFiltration_weak N he F
example {n : SimplexCategory} (F : Obj N n) {i j : Fin (n.len+1)} (f : i ⟶ j) :
    N.coarse.weq ((initialFiltration F.obj).map f) := initialFiltration_map_weak N he F f
example {m n : SimplexCategory} (α : m ⟶ n) (F : Obj N n) :
    initialFiltration ((reindex N α).obj F).obj =
      (SimplexCategory.toCat.map α).toFunctor ⋙ initialFiltration F.obj := initialFiltration_reindex N α F
example (F : Obj N ⦋0⦌) : N.coarse.weq ((initialFiltration F.obj).map (𝟙 (0 : Fin 1))) :=
  initialFiltration_map_weak N he F _
example (n : SimplexCategory) : Obj N n ⥤ ComposableArrows C n.len := initialFiltrationFunctor N n
example {n : SimplexCategory} (F : Obj N n) :
    ((initialFiltrationFunctor N n).obj F).obj 0 = (first N n).obj F := rfl
example {n : SimplexCategory} {F G : Obj N n} (f : F ⟶ G) (i : Fin (n.len+1)) :
    ((initialFiltrationFunctor N n).map f).app i = f.hom.hom.app (interval 0 i.succ (Fin.zero_le _)) := rfl
example {n : SimplexCategory} {F G : Obj N n} (f : F ⟶ G) :
    (waldhausenStructure N n).weq f ↔ ∀ i, V.weq (((initialFiltrationFunctor N n).map f).app i) :=
  weq_iff_initialFiltrationFunctor N f
example {n : SimplexCategory} {F G : Obj N n} (f : F ⟶ G)
    (h : ∀ i, V.weq (((initialFiltrationFunctor N n).map f).app i)) :
    (waldhausenStructure N n).weq f := (weq_iff_initialFiltrationFunctor N f).2 h
example {m n : SimplexCategory} (α : m ⟶ n) :
    reindex N α ⋙ initialFiltrationFunctor N m = initialFiltrationFunctor N n ⋙
      (Functor.whiskeringLeft (Fin (m.len+1)) (Fin (n.len+1)) C).obj
        (SimplexCategory.toCat.map α).toFunctor := initialFiltrationFunctor_reindex N α
end Quillen.Waldhausen.Fibration.RelativeRows

namespace Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)
-- Actual positive chain arrows are the original interval arrows, not replacement maps.
example {n : SimplexCategory} (F : Obj N n) {i j : Fin (n.len+1)} (f : i ⟶ j) :
    ((initialFiltrationFunctor N n).obj F).map f = F.obj.obj.map
      (homOfLE (show interval 0 i.succ (Fin.zero_le _) ≤ interval 0 j.succ (Fin.zero_le _) from
        ⟨le_rfl, Nat.succ_le_succ (leOfHom f)⟩)) := rfl
-- Fine detection needs no coarse extension or saturation premise, even in degree zero.
example {F G : Obj N ⦋0⦌} (f : F ⟶ G) :
    (waldhausenStructure N ⦋0⦌).weq f ↔ V.weq ((first N ⦋0⦌).map f) := by
  rw [weq_iff_initialFiltrationFunctor]
  constructor
  · intro h; exact h 0
  · intro h i
    have hi : i = 0 := by
      apply Fin.ext
      change i.val = 0
      have hi := i.isLt
      change i.val < 1 at hi
      omega
    subst i
    exact h
-- The omitted initial diagonal is handled by its actual zero-object isomorphism.
example {n : SimplexCategory} {F G : Obj N n} (f : F ⟶ G) :
    V.weq (f.hom.hom.app (interval 0 0 le_rfl)) :=
  V.weq_iso _ ((F.obj.property.zero 0).isIso (G.obj.property.zero 0) _)
-- Coarse weakness and fine cofibrancy refer to exactly the same original chain arrow.
example (he : ExtensionAxiom N.coarse) {n : SimplexCategory} (F : Obj N n)
    {i j : Fin (n.len+1)} (f : i ⟶ j) :
    V.cof (((initialFiltrationFunctor N n).obj F).map f) ∧
      N.coarse.weq (((initialFiltrationFunctor N n).obj F).map f) :=
  ⟨initialFiltration_map_cof F.obj f, initialFiltration_map_weak N he F f⟩
-- The actual cofiber square changes only the chosen zero corner.
example {n : SimplexCategory} (F : QuotientRows.Obj V n)
    (i j k : Fin (n.len+1)) (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout
      (F.obj.map (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl,hjk⟩)))
      (N.coarse.isZero.from_ (F.obj.obj (interval i j hij)))
      (F.obj.map (homOfLE (show interval i k (hij.trans hjk) ≤ interval j k hjk from ⟨hij,le_rfl⟩)))
      (N.coarse.isZero.to_ (F.obj.obj (interval j k hjk))) := horizontal_cofiber_isPushout N F i j k hij hjk
end Quillen.Waldhausen.Fibration.RelativeRows
