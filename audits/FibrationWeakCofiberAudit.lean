import Quillen.Waldhausen.Fibration.WeakEquivalenceCofiber
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Waldhausen.Fibration.WeakEquivalenceCofiber
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 17 do throwError "Expected 17 weak-cofiber origins, got {count}"
  logInfo m!"Audited all {count} weak-cofiber declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] (W : Structure C)
example (X : C) : Acyclic W X ↔ W.weq (W.isZero.to_ X) := Iff.rfl
example {X : C} (hX : IsZero X) : Acyclic W X := acyclic_of_isZero W hX
example : Acyclic W W.zero := acyclic_zero W
example {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q} (hi : W.cof i)
    (h : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q))
    (hw : W.weq i) : Acyclic W Q := acyclic_of_weak_of_isPushout W hi h hw
example (he : ExtensionAxiom W) {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (h : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    W.weq i ↔ Acyclic W Q := weak_iff_acyclic_of_isPushout W he hi h
example (he : ExtensionAxiom W) (X : ExtensionCategory.Obj W) :
    W.weq (W.isZero.to_ ((ExtensionCategory.cofiber W).obj X)) ↔ W.weq X.obj.hom :=
  cofiber_acyclic_iff W he X
-- The input remains a structural extension property on actual squares.
example (he : ExtensionAxiom W) {A B Q A' B' Q' : C}
    {i : A ⟶ B} {q : B ⟶ Q} {i' : A' ⟶ B'} {q' : B' ⟶ Q'}
    (hi : W.cof i) (hi' : W.cof i')
    (h : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q))
    (h' : IsPushout i' (W.isZero.from_ A') q' (W.isZero.to_ Q'))
    (a : A ⟶ A') (b : B ⟶ B') (c : Q ⟶ Q')
    (wi : i ≫ b = a ≫ i') (wq : q ≫ c = b ≫ q')
    (ha : W.weq a) (hc : W.weq c) : W.weq b :=
  he.extension hi hi' h h' a b c wi wq ha hc
end Quillen.Waldhausen.Fibration
