import Quillen.Topology.HELP.ContractibleTest
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Topology.HELP.StrictPullback, `Quillen.Topology.HELP.ContractibleTest]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.moduleNames[index.toNat]! do continue
    count := count + 1
    let axioms ← collectAxioms name
    for a in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do throwError "Unsupported {a}: {name}"
    logInfo m!"ACCEPTED {env.header.moduleNames[index.toNat]!} {name}: {axioms}"
  unless count == 11 do throwError "Expected11 contracted-test origins, got {count}"
  logInfo m!"Audited all {count} contracted-test origins."
noncomputable section
open CategoryTheory Quillen Quillen.HomotopyPullback
open scoped Topology unitInterval
universe u
variable {E F B T : Type u}
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace T]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
section Pullback
variable (r : C(T,B)) (d : T)
example (z : {z : T × E // p z.2 = r z.1}) :
    (strictPullbackMapOver p q f sq r z).1 = (z.1.1, f z.1.2) := rfl
example : (strictBaseProjection q r).comp (strictPullbackMapOver p q f sq r) =
    strictBaseProjection p r := rfl
example : (strictSourceProjection q r).comp (strictPullbackMapOver p q f sq r) =
    f.comp (strictSourceProjection p r) := rfl
example : (strictPullbackFiberHomeomorph q r d).toHomotopyEquiv.toFun.comp
    (HomotopyFiber.strictMapOver (strictBaseProjection p r) (strictBaseProjection q r)
      (strictPullbackMapOver p q f sq r) rfl d) =
    (HomotopyFiber.strictMapOver p q f sq (r d)).comp
      (strictPullbackFiberHomeomorph p r d).toHomotopyEquiv.toFun :=
  strictPullbackFiberHomeomorph_naturality p q f sq r d
example (hf : CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq (r d))) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (strictBaseProjection p r) (strictBaseProjection q r)
        (strictPullbackMapOver p q f sq r) rfl d) :=
  strictPullbackMapOver_fiber_compactHELP p q f sq r d hf
end Pullback
section Test
variable (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (d : D) (H : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d))
    (α : C(A,E)) (β : C(D,F)) (w : f.comp α = β.comp i.hom)
example (hf : CompactHomotopyExtensionLiftingProperty
    (HomotopyFiber.strictMapOver p q f sq (q (β d)))) :
    ∃ c : C(D,E), c.comp i.hom = α ∧ Nonempty ((f.comp c).HomotopyRel β (Set.range i)) :=
  strictHELP_on_contracted_test p q f sq hp hq A D i hi d H α β w hf
example (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty
    (HomotopyFiber.strictMapOver p q f sq b)) :
    ∃ c : C(D,E), c.comp i.hom = α ∧ Nonempty ((f.comp c).HomotopyRel β (Set.range i)) :=
  strictHELP_on_contracted_test_of_all_fibers p q f sq hp hq hf A D i hi d H α β w
example (hf : CompactHomotopyExtensionLiftingProperty
    (HomotopyFiber.strictMapOver p q f sq (q (β d)))) :
    ∃ c : C(D,E), c.comp i.hom = α ∧ ∃ K : (f.comp c).Homotopy β,
      ∀ t x, K (t, i x) = f (α x) :=
  strictHELP_on_contracted_test_boundary p q f sq hp hq A D i hi d H α β w hf
example (hf : CompactHomotopyExtensionLiftingProperty
    (HomotopyFiber.strictMapOver p q f sq (q (β d)))) :
    ∃ c : C(D,E), c.comp i.hom = α ∧ ∃ K : (f.comp c).Homotopy β,
      ∀ t x, K (t, i x) = β (i x) := by
  obtain ⟨c, hc, K, hK⟩ := strictHELP_on_contracted_test_boundary p q f sq hp hq A D i hi d H α β w hf
  exact ⟨c, hc, K, fun t x ↦ (hK t x).trans (ContinuousMap.congr_fun w x)⟩
end Test
section EmptyBoundary
variable (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (D : TopCat.{u}) [CompactSpace D] (d : D)
    (H : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d)) (β : C(D,F))
example (hf : CompactHomotopyExtensionLiftingProperty
    (HomotopyFiber.strictMapOver p q f sq (q (β d)))) :
    ∃ c : C(D,E), Nonempty ((f.comp c).Homotopy β) := by
  let A := TopCat.of PEmpty.{u+1}
  let i : A ⟶ D := TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩
  have hi : TheoremA.homotopyExtensionProperty i := by
    apply TheoremA.homotopyExtensionProperty_of_continuous
    intro Z b H _
    exact ⟨b.comp ContinuousMap.snd, fun _ ↦ rfl, fun _ x ↦ isEmptyElim x⟩
  let α : C(A,E) := ⟨isEmptyElim, continuous_of_discreteTopology⟩
  have w : f.comp α = β.comp i.hom := by ext x; exact isEmptyElim x
  obtain ⟨c, _, ⟨K⟩⟩ := strictHELP_on_contracted_test p q f sq hp hq A D i hi d H α β w hf
  exact ⟨c, ⟨K.toHomotopy⟩⟩
end EmptyBoundary
