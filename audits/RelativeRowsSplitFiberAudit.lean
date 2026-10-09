import Quillen.Waldhausen.SConstruction.Rows.OneRow
import Quillen.Waldhausen.Fibration.RelativeRows.SplitFiber
import Quillen.Waldhausen.Fibration.RelativeRows.SplitFiberZero
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.SConstruction.Rows.OneRow, `Quillen.Waldhausen.Fibration.RelativeRows.SplitFiber, `Quillen.Waldhausen.Fibration.RelativeRows.SplitFiberZero]
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
  unless count == 35 do throwError "Expected 35 split-row origins, got {count}"
  logInfo m!"Audited all {count} split-fiber-row declaration origins."
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen
variable {C : Type u} [Category.{v} C] (W : Structure C)
example (X : C) : ((QuotientRows.oneEmbedding W).obj X).obj.obj (interval 0 1 (by decide)) = X := rfl
example (X : C) : ((QuotientRows.oneEmbedding W).obj X).obj.obj (interval 0 0 le_rfl) = W.zero := rfl
example (X : C) : ((QuotientRows.oneEmbedding W).obj X).obj.obj (interval 1 1 le_rfl) = W.zero := rfl
example {X Y : C} (f : X ⟶ Y) : ((QuotientRows.oneEmbedding W).map f).hom.app (interval 0 1 (by decide)) = f := rfl
example : IsExact W.cof W.weq (QuotientRows.waldhausenStructure W ⦋1⦌).cof
    (QuotientRows.waldhausenStructure W ⦋1⦌).weq (QuotientRows.oneEmbedding W) := QuotientRows.oneEmbedding_exact W
example : (QuotientRows.oneEmbedding W).obj W.zero = QuotientRows.zero W ⦋1⦌ := QuotientRows.oneEmbedding_zero W
namespace Fibration.RelativeRows
variable (N : NestedWeakEquivalences W) (n : SimplexCategory)
example : (fiberOrdinal n).toOrderHom 0 = 0 := rfl
example (i : Fin (n.len + 1)) : (fiberOrdinal n).toOrderHom i.succ = 1 := rfl
example {m : SimplexCategory} (α : m ⟶ n) : addInitial.map α ≫ fiberOrdinal n = fiberOrdinal m := fiberOrdinal_naturality α
example : fiber N n ⋙ forget N n = fiberUnderlying (V := W) n := rfl
example (X : C) : ((fiber N n).obj X).obj.obj.obj (firstInterval n) = X := rfl
example {X Y : C} (f : X ⟶ Y) : ((fiber N n).map f).hom.hom.app (firstInterval n) = f := rfl
example (X : C) (p : Interval n) : ((fiber N n).obj X).obj.obj.obj ((QuotientRows.indexMap (tail.app n)).obj p) = W.zero := rfl
example {X Y : C} (f : X ⟶ Y) (p : Interval n) : ((fiber N n).map f).hom.hom.app ((QuotientRows.indexMap (tail.app n)).obj p) = 𝟙 W.zero := rfl
example : IsExact W.cof W.weq (waldhausenStructure N n).cof (waldhausenStructure N n).weq (fiber N n) := fiber_exact N n
example : fiber N n ⋙ first N n = 𝟭 C := fiber_first N n
example : fiber N n ⋙ tailFunctor N n = (Functor.const C).obj (QuotientRows.zero (acyclicStructure N) n) := fiber_tail N n
example {m : SimplexCategory} (α : m ⟶ n) : fiber N n ⋙ reindex N α = fiber N m := fiber_reindex N α
example : fiber N n ⋙ firstTail N n = (𝟭 C).prod' ((Functor.const C).obj (QuotientRows.zero (acyclicStructure N) n)) := fiber_firstTail N n
example : (fiber N n).obj W.zero = zero N n := fiber_zero N n
end Fibration.RelativeRows
end Quillen.Waldhausen
