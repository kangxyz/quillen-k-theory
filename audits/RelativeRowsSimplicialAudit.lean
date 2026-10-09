import Quillen.Waldhausen.Fibration.RelativeRows.TailSection
import Quillen.Waldhausen.Fibration.RelativeRows.Simplicial
import Quillen.Waldhausen.Fibration.RelativeRows.FirstTailSSet
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.TailSection, `Quillen.Waldhausen.Fibration.RelativeRows.Simplicial, `Quillen.Waldhausen.Fibration.RelativeRows.FirstTailSSet]
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
  unless count == 55 do throwError "Expected 55 relative S-row origins, got {count}"
  logInfo m!"Audited all {count} relative-row-S-map declaration origins."
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RelativeRows
section Independent
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V) (n : SimplexCategory)
example (i : Fin (n.len+1)) : (dropInitial n).toOrderHom i.succ = i := rfl
example : tail.app n ≫ dropInitial n = 𝟙 n := tail_dropInitial n
example : tailSection N n ⋙ forget N n = tailSectionUnderlying N n := rfl
example : IsExact (QuotientRows.waldhausenStructure (acyclicStructure N) n).cof
    (QuotientRows.waldhausenStructure (acyclicStructure N) n).weq
    (waldhausenStructure N n).cof (waldhausenStructure N n).weq (tailSection N n) := tailSection_exact N n
example : tailSection N n ⋙ tailFunctor N n = 𝟭 _ := tailSection_tail N n
example (X : QuotientRows.Obj (acyclicStructure N) n) : IsZero ((first N n).obj ((tailSection N n).obj X)) := tailSection_first_isZero N n X
example : (tailSection N n).obj (QuotientRows.zero (acyclicStructure N) n) = zero N n := tailSection_zero N n
end Independent
section Common
variable {C : Type u} [Category.{u} C] {V : Structure C} (N : NestedWeakEquivalences V) (n : SimplexCategory)
example : (relativeSRows N).obj (op n) = sSet (waldhausenStructure N n).cof (waldhausenStructure N n).weq := rfl
example {m : SimplexCategory} (α : m ⟶ n) : (relativeSRows N).map α.op = sSetMap (reindex_exact N α) := rfl
example : (tailSRows N).app (op n) = sSetMap (tailFunctor_exact N n) := rfl
example : (fiberSRows N).app (op n) = sSetMap (fiber_exact N n) := rfl
example : fiberSRows N ≫ tailSRows N = zeroSRows (V := V) (acyclicStructure N) := fiberSRows_tailSRows N
example {m : SimplexCategory} (α : m ⟶ n) : (tailSRows N).app (op n) ≫ (ordinarySRows (acyclicStructure N)).map α.op = (relativeSRows N).map α.op ≫ (tailSRows N).app (op m) := ((tailSRows N).naturality α.op).symm
example {m : SimplexCategory} (α : m ⟶ n) : (fiberSRows N).app (op n) ≫ (relativeSRows N).map α.op = (fiberSRows N).app (op m) := by simpa using ((fiberSRows N).naturality α.op).symm
example : firstTailSSet N n = sSetMap (firstTail_exact N n) ≫ Product.comparison V (QuotientRows.waldhausenStructure (acyclicStructure N) n) := rfl
example : firstTailSSet N n ≫ snd _ _ = (tailSRows N).app (op n) := firstTailSSet_snd N n
example : firstTailSSet N n ≫ fst _ _ = sSetMap (first_exact N n) := firstTailSSet_fst N n
example : (fiberSRows N).app (op n) ≫ firstTailSSet N n = ProductRealization.vertexSection (sSet V.cof V.weq) ((ordinarySRows (acyclicStructure N)).obj (op n)) (tailZeroVertex N n) := fiber_firstTailSSet N n
example : PathConnectedSpace |(relativeSRows N).obj (op n)| := inferInstance
example : PathConnectedSpace |(ordinarySRows (acyclicStructure N)).obj (op n)| := inferInstance
example (k : SimplexCategoryᵒᵖ) (X : ((relativeSRows N).obj (op n)).obj k) : (((tailSRows N).app (op n)).app k X).val = X.val ⋙ tailFunctor N n := rfl
example (k : SimplexCategoryᵒᵖ) (X : (sSet V.cof V.weq).obj k) : (((fiberSRows N).app (op n)).app k X).val = X.val ⋙ fiber N n := rfl
end Common
end Quillen.Waldhausen.Fibration.RelativeRows
