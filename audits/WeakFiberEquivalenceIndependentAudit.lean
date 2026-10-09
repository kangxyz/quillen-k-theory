import Quillen.Topology.HomotopyFiber.WeakSourceEquivalence
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Topology.HomotopyGroups.WeakEquivalenceCancellation,
    `Quillen.Topology.HomotopyGroups.ComponentCriterion, `Quillen.Topology.HomotopyFiber.WeakFibers,
    `Quillen.Topology.HomotopyFiber.WeakCriterion, `Quillen.Topology.HomotopyFiber.WeakPullback,
    `Quillen.Topology.HomotopyFiber.ProjectionFibration,
    `Quillen.Topology.HomotopyFiber.WeakSourceEquivalence]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.moduleNames[index.toNat]! do continue
    count := count + 1
    let axioms ← collectAxioms name
    for a in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unsupported {a}: {name}"
    logInfo m!"ACCEPTED {env.header.moduleNames[index.toNat]!} {name}: {axioms}"
  unless count == 40 do throwError "Expected 40 weak fiber origins, got {count}"
  logInfo m!"Audited all {count} weak fiber equivalence origins."
noncomputable section
open Quillen
open scoped Topology unitInterval
universe u v w
section Universes
variable {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X,Y)) (g : C(Y,Z))
example (hgf : IsWeakHomotopyEquivalence (g.comp f)) (hf : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence g := hgf.of_comp_left hf
example (hgf : IsWeakHomotopyEquivalence (g.comp f)) (hg : IsWeakHomotopyEquivalence g) :
    IsWeakHomotopyEquivalence f := hgf.of_comp_right hg
example (x x' : X) (h0 : Function.Injective (homotopyGroupMap (N := Fin 0) f (x := x) rfl))
    (h : Joined (f x) (f x')) : Joined x x' := joined_of_homotopyGroupMap_zero_injective f x x' h0 h
example (hs : ∀ y, ∃ x, Joined (f x) y)
    (hi : ∀ x x', Joined (f x) (f x') → Joined x x') (x : X) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) f (x := x) rfl) :=
  homotopyGroupMap_zero_bijective_of_components f hs hi x
example [IsEmpty X] (h : IsWeakHomotopyEquivalence f) : IsEmpty Y := h.isEmpty_target
example [IsEmpty X] (y : Y) : ¬ IsWeakHomotopyEquivalence f := by
  intro h
  obtain ⟨x, _⟩ := h.component_surjective y
  exact isEmptyElim x
example [IsEmpty Y] : IsWeakHomotopyEquivalence f :=
  ⟨fun y ↦ isEmptyElim y, fun x _ ↦ False.elim (isEmptyElim (f x))⟩
end Universes
section Fibers
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
variable (f : C(X,B)) (g : C(Y,B)) (m : C(X,Y)) (sq : g.comp m = f) (b : B)
variable (hf : IsWeakHomotopyEquivalence f) (hm : IsWeakHomotopyEquivalence m)
example : IsWeakHomotopyEquivalence (MappingPath.endpoint f) :=
  MappingPath.endpoint_isWeakHomotopyEquivalence f hf
example (x : X) : MappingPath.endpoint f (MappingPath.inclusion f x) = f x := rfl
example (hl : HomotopyLiftingProperty f) (z : {x : X // f x = b}) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi n {x : X // f x = b} z) :=
  HomotopyFiber.subsingleton_strictFiber_of_weak_fibration f hf hl b z n
example (z : HomotopyFiber f b) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi n (HomotopyFiber f b) z) :=
  HomotopyFiber.subsingleton_of_weakEquivalence f hf b z n
example (z : HomotopyFiber f b) : Subsingleton (HomotopyGroup.Pi 0 (HomotopyFiber f b) z) :=
  HomotopyFiber.subsingleton_of_weakEquivalence f hf b z 0
example : Nonempty (HomotopyFiber f b) := HomotopyFiber.nonempty_of_weakEquivalence f hf b
example : PathConnectedSpace (HomotopyFiber f b) := HomotopyFiber.pathConnectedSpace_of_weakEquivalence f hf b
example : IsWeakHomotopyEquivalence f ↔
    (∀ b, Nonempty (HomotopyFiber f b)) ∧
    (∀ b (z : HomotopyFiber f b) n, Subsingleton (HomotopyGroup.Pi n (HomotopyFiber f b) z)) :=
  HomotopyFiber.isWeakHomotopyEquivalence_iff_fibers f
example : IsWeakHomotopyEquivalence (HomotopyPullback.baseProjection f g) :=
  HomotopyPullback.baseProjection_isWeakHomotopyEquivalence f g hf
example : HomotopyLiftingProperty (HomotopyFiber.projection f b) :=
  HomotopyFiber.projection_homotopyLiftingProperty f b
example : (HomotopyPullback.baseProjection (ContinuousMap.const (ULift.{u} Unit) b) f).comp
    (HomotopyFiber.projectionPullbackHomeomorph f b : C(_, _)) = HomotopyFiber.projection f b := rfl
example : IsWeakHomotopyEquivalence (HomotopyFiber.mapOver f g m sq b) :=
  HomotopyFiber.mapOver_isWeakHomotopyEquivalence f g m sq b hm
example (z : HomotopyFiber f b) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (HomotopyFiber.mapOver f g m sq b) (x := z) rfl) :=
  HomotopyFiber.homotopyGroupMap_mapOver_bijective f g m sq b hm z n
example (z : HomotopyFiber f b) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (HomotopyFiber.mapOver f g m sq b) (x := z) rfl) :=
  HomotopyFiber.homotopyGroupMap_mapOver_bijective f g m sq b hm z 0
example (z : HomotopyFiber f b) : (HomotopyFiber.mapOver f g m sq b z).1.1 = m z.1.1 := rfl
example (z : HomotopyFiber f b) : (HomotopyFiber.mapOver f g m sq b z).1.2 = z.1.2 := rfl
example (z : HomotopyFiber f b) : (HomotopyFiber.sourcePullbackHomeomorph f g m sq b z).1.2 =
    HomotopyFiber.mapOver f g m sq b z := rfl
example [IsEmpty (HomotopyFiber f b)] : IsEmpty (HomotopyFiber g b) :=
  (HomotopyFiber.mapOver_isWeakHomotopyEquivalence f g m sq b hm).isEmpty_target
example [IsEmpty (HomotopyFiber g b)] : IsEmpty (HomotopyFiber f b) :=
  ⟨fun z ↦ isEmptyElim (HomotopyFiber.mapOver f g m sq b z)⟩
example (z : HomotopyFiber g b) : Nonempty (HomotopyFiber f b) := by
  obtain ⟨x, _⟩ := (HomotopyFiber.mapOver_isWeakHomotopyEquivalence f g m sq b hm).component_surjective z
  exact ⟨x⟩
end Fibers
section RightProper
variable {E A B : Type u} [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]
    (p : C(E,B)) (m : C(A,B)) (hp : HomotopyLiftingProperty p) (hm : IsWeakHomotopyEquivalence m)
example : IsWeakHomotopyEquivalence (HomotopyPullback.strictSourceProjection p m) :=
  HomotopyPullback.strictSourceProjection_isWeakHomotopyEquivalence p m hp hm
example (z : {z : A × E // p z.2 = m z.1}) : HomotopyPullback.strictSourceProjection p m z = z.1.2 := rfl
example [IsEmpty {z : A × E // p z.2 = m z.1}] : IsEmpty E :=
  (HomotopyPullback.strictSourceProjection_isWeakHomotopyEquivalence p m hp hm).isEmpty_target
end RightProper
