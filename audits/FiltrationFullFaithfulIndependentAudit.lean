import Quillen.Waldhausen.Fibration.RelativeRows.FiltrationFullFaithful
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.FiltrationFullFaithful]
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
  unless count == 49 do throwError "Expected 49 filtration-full-faithfulness origins, got {count}"
  logInfo m!"Audited all {count} relative-filtration-full-faithfulness declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (n : SimplexCategory)
example : (initialFiltrationFunctor N n).Full := inferInstance
example : (initialFiltrationFunctor N n).Faithful := inferInstance
example : (initialFiltrationFunctor N n).FullyFaithful := initialFiltrationFullyFaithful N n
variable {F G : Obj N n}
  (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G)
example : (initialFiltrationFullyFaithful N n).preimage a = extendFiltrationMap N a := rfl
example : (initialFiltrationFullyFaithful N n).homEquiv.symm a = extendFiltrationMap N a := rfl
example : (initialFiltrationFunctor N n).map (extendFiltrationMap N a) = a :=
  initialFiltrationFunctor_map_extend N a
example (f : F ⟶ G) : extendFiltrationMap N ((initialFiltrationFunctor N n).map f) = f :=
  (initialFiltrationFullyFaithful N n).preimage_map f
example (i : Fin (n.len+1)) :
    ((extendFiltrationMap N a).hom.hom.app (interval 0 i.succ (Fin.zero_le _))) = a.app i :=
  extendFiltrationAt_initial N a i
example (p : Interval (addInitial.obj n)) :
    originalQuotient N F p ≫ (extendFiltrationMap N a).hom.hom.app p =
      (augmentFiltrationMap N a).app p.val.2 ≫ originalQuotient N G p :=
  originalQuotient_extendFiltrationAt N a p
example : (augmentFiltrationMap N a).app 0 = (F.obj.property.zero 0).to_ _ := rfl
example (ha : ∀ i, V.weq (a.app i)) : (waldhausenStructure N n).weq (extendFiltrationMap N a) :=
  extendFiltrationMap_weak N a ha
example (f : F ⟶ G) (h : (initialFiltrationFunctor N n).map f = a) : f = extendFiltrationMap N a := by
  apply (initialFiltrationFunctor N n).map_injective
  rw [initialFiltrationFunctor_map_extend, h]
end Quillen.Waldhausen.Fibration.RelativeRows
