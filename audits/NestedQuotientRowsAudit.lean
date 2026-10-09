import Quillen.Waldhausen.Fibration.Rows.NestedWeakEquivalences
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.Rows.NestedWeakEquivalences]
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
  unless count == 20 do
    throwError "Expected exactly 20 same-type-nested-row origins, found {count}"
  logInfo m!"Audited all {count} same-type-nested-row declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RowWeakEquivalences
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (n : SimplexCategory)
example : Structure (QuotientRows.Obj V n) := coarseStructure N n
example : (coarseStructure N n).cof = (QuotientRows.waldhausenStructure V n).cof := rfl
example : (coarseStructure N n).zero = QuotientRows.zero V n := rfl
example {F G : QuotientRows.Obj V n} (f : F ⟶ G) :
    (coarseStructure N n).weq f ↔ ∀ p, N.coarse.weq (f.hom.app p) := Iff.rfl
example : NestedWeakEquivalences (QuotientRows.waldhausenStructure V n) := nested N n
example : (nested N n).coarse = coarseStructure N n := rfl
example {F G : QuotientRows.Obj V n} (f : F ⟶ G)
    (hf : (QuotientRows.waldhausenStructure V n).weq f) : (coarseStructure N n).weq f :=
  (nested N n).le_weq f hf
example (p : Interval n) : IsExact (coarseStructure N n).cof (coarseStructure N n).weq
    N.coarse.cof N.coarse.weq (QuotientRows.evaluation V p) := evaluation_coarse_exact N p
example {m : SimplexCategory} (α : m ⟶ n) :
    IsExact (coarseStructure N n).cof (coarseStructure N n).weq
      (coarseStructure N m).cof (coarseStructure N m).weq (QuotientRows.reindex V α) := reindex_coarse_exact N α
example [N.coarse.weq.HasTwoOutOfThreeProperty] : (coarseStructure N n).weq.HasTwoOutOfThreeProperty := inferInstance
example (p : Interval n) {F G : QuotientRows.Obj V n} (f : F ⟶ G) :
    (QuotientRows.evaluation V p).map f = f.hom.app p := rfl
example {m : SimplexCategory} (α : m ⟶ n) {F G : QuotientRows.Obj V n} (f : F ⟶ G)
    (p : Interval m) : ((QuotientRows.reindex V α).map f).hom.app p =
      f.hom.app ((QuotientRows.indexMap α).obj p) := rfl
example : (coarseStructure N ⦋0⦌).zero = QuotientRows.zero V ⦋0⦌ := rfl
example (p : Interval n) {F G H T : QuotientRows.Obj V n}
    {f : F ⟶ G} {g : F ⟶ H} {i : G ⟶ T} {j : H ⟶ T}
    (hf : QuotientRows.cof V n f) (h : IsPushout f g i j) :
    IsPushout (f.hom.app p) (g.hom.app p) (i.hom.app p) (j.hom.app p) :=
  (evaluation_coarse_exact N p).pushout hf h
example {m : SimplexCategory} (α : m ⟶ n)
    {F G H T : QuotientRows.Obj V n} {f : F ⟶ G} {g : F ⟶ H}
    {i : G ⟶ T} {j : H ⟶ T} (hf : QuotientRows.cof V n f)
    (h : IsPushout f g i j) :
    IsPushout ((QuotientRows.reindex V α).map f) ((QuotientRows.reindex V α).map g)
      ((QuotientRows.reindex V α).map i) ((QuotientRows.reindex V α).map j) :=
  (reindex_coarse_exact N α).pushout hf h
end Quillen.Waldhausen.Fibration.RowWeakEquivalences
