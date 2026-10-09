import Quillen.Topology.HELP.FiberwiseRealizationEquivalence
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.HELP.StrictPair,
    `Quillen.Topology.HELP.ContractibleTestFull, `Quillen.Topology.HELP.PairLifting,
    `Quillen.Topology.HELP.FiberwiseRealizationLifting,
    `Quillen.Topology.HELP.FiberwiseRealizationEquivalence]
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
  unless count == 18 do throwError "Expected18 fiberwise-realization origins, got {count}"
  logInfo m!"Audited all {count} fiberwise-realization origins."
noncomputable section
open CategoryTheory Quillen
open scoped Simplicial Topology unitInterval
universe u
section Pair
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  (f : C(E,F)) (A D : TopCat.{u}) (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
example (hf : ∀ (a : C(A,E)) (b : C(D,F)), f.comp a = b.comp i.hom →
    ∃ c : C(D,E), c.comp i.hom = a ∧ Nonempty ((f.comp c).HomotopyRel b (Set.range i)))
    (a : C(A,E)) (b : C(D,F)) (H : (f.comp a).Homotopy (b.comp i.hom)) :
    ∃ c : C(D,E), c.comp i.hom = a ∧ ∃ K : (f.comp c).Homotopy b,
      ∀ t x, K (t,i x) = H (t,x) := fullHELP_at_pair_of_strict f A D i hi hf a b H
example (hf : ∀ (a : C(A,E)) (b : C(D,F)) (H : (f.comp a).Homotopy (b.comp i.hom)),
    ∃ c : C(D,E), c.comp i.hom = a ∧ ∃ K : (f.comp c).Homotopy b,
      ∀ t x, K (t,i x) = H (t,x)) :
    HasLiftingProperty i (TopCat.ofHom (MappingPath.endpoint f)) :=
  MappingPath.endpoint_hasLiftingProperty_of_pairHELP f i hf
end Pair
section Fiber
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
  (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
  (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b))
example (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (d : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d))
    (a : C(A,E)) (b : C(D,F)) (H : (f.comp a).Homotopy (b.comp i.hom)) :
    ∃ c : C(D,E), c.comp i.hom = a ∧ ∃ K : (f.comp c).Homotopy b,
      ∀ t x, K (t,i x) = H (t,x) :=
  fullHELP_on_contracted_test p q f sq hp hq hf A D i hi d HD a b H
example {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i) (TopCat.ofHom (MappingPath.endpoint f)) :=
  MappingPath.endpoint_realization_mono_of_fiberHELP p q f sq hp hq hf i
example (n : ℕ) : HasLiftingProperty (SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u})))
    (TopCat.ofHom (MappingPath.endpoint f)) :=
  MappingPath.endpoint_realization_mono_of_fiberHELP p q f sq hp hq hf _
example : HasLiftingProperty (SSet.toTop.map (∂Δ[0].ι : _ ⟶ (Δ[0] : SSet.{u})))
    (TopCat.ofHom (MappingPath.endpoint f)) :=
  MappingPath.endpoint_realization_mono_of_fiberHELP p q f sq hp hq hf _
example {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (a : |X| ⟶ TopCat.of (MappingPath f)) (b : |Y| ⟶ TopCat.of F)
    (w : CommSq a (SSet.toTop.map i) (TopCat.ofHom (MappingPath.endpoint f)) b) :
    ∃ l : |Y| ⟶ TopCat.of (MappingPath f), SSet.toTop.map i ≫ l = a ∧
      l ≫ TopCat.ofHom (MappingPath.endpoint f) = b := by
  let := MappingPath.endpoint_realization_mono_of_fiberHELP p q f sq hp hq hf i
  exact ⟨w.lift, w.fac_left, w.fac_right⟩
end Fiber
section Equivalence
variable {X Y : SSet.{u}} {B : Type u} [TopologicalSpace B]
  (p : C(|X|,B)) (q : C(|Y|,B)) (f : C(|X|,|Y|)) (sq : q.comp f = p)
  (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
  (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b))
example : ContinuousMap.HomotopyEquiv |X| |Y| := homotopyEquivOfRealizationFiberHELP p q f sq hp hq hf
example : (homotopyEquivOfRealizationFiberHELP p q f sq hp hq hf).toFun = f := rfl
example : ((homotopyEquivOfRealizationFiberHELP p q f sq hp hq hf).invFun.comp f).Homotopic
    (ContinuousMap.id |X|) := (homotopyEquivOfRealizationFiberHELP p q f sq hp hq hf).left_inv
example : (f.comp (homotopyEquivOfRealizationFiberHELP p q f sq hp hq hf).invFun).Homotopic
    (ContinuousMap.id |Y|) := (homotopyEquivOfRealizationFiberHELP p q f sq hp hq hf).right_inv
example (x : |X|) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) f (x := x) rfl) :=
  homotopyGroupMap_bijective_of_homotopyEquiv (homotopyEquivOfRealizationFiberHELP p q f sq hp hq hf) rfl n
end Equivalence
