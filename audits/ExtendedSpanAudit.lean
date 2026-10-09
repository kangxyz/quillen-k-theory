import Quillen.Waldhausen.QuillenComparison.ExtendedSpan
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Waldhausen.QuillenComparison.ExtendedSpan
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count = 24 do throwError "Expected frozen 24-declaration scope; audited {count}"
  logInfo m!"Audited all {count} ExtendedSpan declaration origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
namespace Quillen.Waldhausen.QuillenComparison
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C) {n : ℕ}
variable (A : Fin (n + 1) ⥤ C)
variable (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
variable {P Z : C} (p : P ⟶ A.obj (Fin.last n)) (hp : E.deflation p)
variable (r : P ⟶ Z) (hr : E.inflation r)
example : (extendedRepresentative E A hA p hp r hr).l =
    p ≫ flagQuotient E A hA (interval 0 (Fin.last n) (Fin.zero_le _)) := rfl
example : (extendedRepresentative E A hA p hp r hr).r = r := rfl
example :
    Q.mkHom E.deflation E.inflation
        (wholeSpan E (extendedRow E A hA p hp r hr) (extendedMiddleInterval n)) ≫
      (E.qIsoOfIso (extendedRowTopIso E A hA p hp r hr)).hom =
    (E.qIsoOfIso ((extendedRowMiddleIso E A hA p hp r hr).app
        (interval 0 (Fin.last n) (Fin.zero_le _)))).hom ≫
      Q.mkHom E.deflation E.inflation (extendedRepresentative E A hA p hp r hr) :=
  extendedRow_wholeSpan E A hA p hp r hr
example (F : Row E ⦋n⦌) {P Z : C}
    (p : P ⟶ (initialFlag E F).obj (Fin.last n)) (hp : E.deflation p)
    (r : P ⟶ Z) (hr : E.inflation r) :
    Q.mkHom E.deflation E.inflation
      (extendedRepresentative E (initialFlag E F) (initialFlag_inflation E F) p hp r hr) =
    (E.qIsoOfIso ((completedInitialIso E F).app
      (interval 0 (Fin.last n) (Fin.zero_le _)))).hom ≫
      Q.mkHom E.deflation E.inflation
        ({ apex := P, l := p, r := r, wl := hp, wr := hr } :
          Span E.deflation E.inflation ((initialFlag E F).obj (Fin.last n)) Z) :=
  extendedRepresentative_initialFlag E F p hp r hr
end Quillen.Waldhausen.QuillenComparison
