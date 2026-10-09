import Lean.Util.CollectAxioms
import Quillen.Topology.Realization.ProductFiberHELP
import Quillen.Topology.HomotopyFiber.FiberDetection
import Quillen.Topology.HomotopyFiber.Connected

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`Quillen.Topology.Realization.SplitFiber,
    `Quillen.Topology.HELP.CompactLifting,
    `Quillen.Topology.Realization.ProductCompactHELP,
    `Quillen.Topology.HELP.Composition,
    `Quillen.Topology.HomotopyFiber.CompactHELP,
    `Quillen.Topology.HomotopyFiber.GroupDetection,
    `Quillen.Topology.HomotopyGroups.ZeroDetection,
    `Quillen.Topology.Realization.ProductFiberHELP,
    `Quillen.Topology.HomotopyFiber.FiberDetection,
    `Quillen.Topology.HomotopyFiber.Connected]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    seen := seen.insert origin
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless seen.size == 10 do throwError "Missing defining module"
  unless count == 39 do throwError "Expected exactly 39 origin declarations, found {count}"
  logInfo m!"Audited all {count} origins of the ten relative-fiber calculus modules."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Quillen
open scoped Simplicial Topology
universe u v w
section Product
variable (A B : SSet.{u})
example : CompactHomotopyExtensionLiftingProperty (ProductRealization.comparison A B) :=
  ProductRealization.comparison_compactHELP A B
example (T : Type v) [TopologicalSpace T] [CompactSpace T] (f : C(T, |A| × |B|)) :
    ∃ g : C(T, |A ⊗ B|), (ProductRealization.comparison A B).comp g = f :=
  ProductRealization.comparison_compact_lifts_universe A B T f
example (b : |B|) : CompactHomotopyExtensionLiftingProperty (ProductRealization.fiberProjection A B b) :=
  ProductRealization.fiberProjection_compactHELP A B b
end Product
section Split
open SplitRealizationFiber
variable {A B E : SSet.{u}} (χ : E ⟶ A ⊗ B) (s : A ⟶ E) (y : B _⦋0⦌)
  (hs : s ≫ χ = ProductRealization.vertexSection A B y)
  (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|) (he : e.toFun = (SSet.toTop.map χ).hom)
example (x : |A|) (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) (inclusion χ s y hs) (x := x) rfl) :=
  inclusion_bijective χ s y hs e he x n
example (x : |A|) : Function.Bijective
    (homotopyGroupMap (N := Fin 0) (inclusion χ s y hs) (x := x) rfl) :=
  inclusion_bijective χ s y hs e he x 0
example (x : |A|) : (inclusion χ s y hs x).1.2 = ContinuousMap.const _ (realizationPoint y) := rfl
example (b : |B|) : CompactHomotopyExtensionLiftingProperty (firstProjection χ b) :=
  firstProjection_compactHELP χ e he b
example [PathConnectedSpace |A|] (b : |B|) (p : HomotopyFiber (projection χ) b) :
    PathConnectedSpace (HomotopyFiber (projection χ) b) := fiber_pathConnected χ e he b p
end Split
section Detection
open HomotopyFiber
variable {X : Type u} {Y : Type v} {B : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (f : C(X, B)) (g : C(Y, B)) (m : C(X, Y)) (sq : g.comp m = f)
  (x : X) (b : B) (hx : f x = b)
example (h₁ : Function.Bijective (homotopyGroupMap (N := Fin 1)
    (mapOver f g m sq b) (mapOver_basepoint f g m sq x b hx)))
    (h₀ : Function.Injective (homotopyGroupMap (N := Fin 0)
      (mapOver f g m sq b) (mapOver_basepoint f g m sq x b hx))) :
    Function.Bijective (piMap 0 m (x := x) rfl) :=
  piMap_bijective_of_fiberMap f g m sq x b hx 0 h₁ h₀
example [PathConnectedSpace X] [PathConnectedSpace Y]
    (h : ∀ n, Function.Bijective (homotopyGroupMap (N := Fin n)
      (mapOver f g m sq b) (mapOver_basepoint f g m sq x b hx))) (x' : X) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) m (x := x') rfl) :=
  homotopyGroupMap_bijective_at_all_points_of_fiberMap f g m sq x b hx h x' n
end Detection
