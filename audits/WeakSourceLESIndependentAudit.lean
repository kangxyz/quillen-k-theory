import Lean.Util.CollectAxioms
import Quillen.Topology.HomotopyFiber.WeakSourcePositive
import Quillen.Topology.HomotopyFiber.WeakContractibility
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.Topology.HomotopyFiber.WeakSourcePositive,
    `Quillen.Topology.HomotopyFiber.WeakContractibility]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    count := count + 1
    seen := seen.insert origin
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless seen.size == 2 do throwError "Missing defining module"
  unless count == 5 do throwError "Expected exactly five origins, found {count}"
  logInfo m!"Audited all {count} origins of the weak-source LES pair."
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Quillen Quillen.HomotopyFiber
open scoped Topology
universe u v w
section Source
variable {X : Type u} {Y : Type v} {B : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (f : C(X,B)) (g : C(Y,B)) (u : C(X,Y)) (sq : g.comp u = f)
  (x : X) (b : B) (hx : f x = b)
example (p : HomotopyFiber f b) : (mapOver f g u sq b p).1.2 = p.1.2 := rfl
example (p : HomotopyFiber f b) : (mapOver f g u sq b p).1.1 = u p.1.1 := rfl
example (n : ℕ) (hc : Function.Bijective (piMap n u (x := x) rfl))
    (hn : Function.Surjective (piMap (n+1) u (x := x) rfl)) :
    Function.Bijective (piMap n (mapOver f g u sq b) (mapOver_basepoint f g u sq x b hx)) :=
  piMap_mapOver_bijective f g u sq x b hx n hc hn
example (hc : Function.Bijective (piMap 0 u (x := x) rfl))
    (hn : Function.Surjective (piMap 1 u (x := x) rfl)) :
    Function.Bijective (homotopyGroupMap (N := Fin 1) (mapOver f g u sq b)
      (mapOver_basepoint f g u sq x b hx)) := piMap_mapOver_bijective f g u sq x b hx 0 hc hn
end Source
section Contractibility
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X,Y)) (y : Y) (x : X) (h : f x = y)
example (n : ℕ) (hi : Function.Injective (homotopyGroupMap (N := Fin n) f h))
    (hs : Function.Surjective (homotopyGroupMap (N := Fin (n+1)) f h)) :
    Subsingleton (HomotopyGroup.Pi n (HomotopyFiber f y) (basepoint f y x h)) :=
  subsingleton_homotopyGroup_of_adjacent f y x h n hi hs
example (hi : Function.Injective (homotopyGroupMap (N := Fin 0) f h))
    (hs : Function.Surjective (homotopyGroupMap (N := Fin 1) f h)) :
    Subsingleton (HomotopyGroup.Pi 0 (HomotopyFiber f y) (basepoint f y x h)) :=
  subsingleton_homotopyGroup_of_adjacent f y x h 0 hi hs
example (hi : Function.Injective (homotopyGroupMap (N := Fin 0) f h))
    (hs : Function.Surjective (homotopyGroupMap (N := Fin 1) f h)) :
    PathConnectedSpace (HomotopyFiber f y) := pathConnectedSpace_of_adjacent f y x h hi hs
example (hf : IsWeakHomotopyEquivalence f) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi n (HomotopyFiber f (f x)) (basepoint f (f x) x rfl)) :=
  subsingleton_homotopyGroup_of_weakEquivalence f x hf n
example (n : ℕ)
    [Subsingleton (HomotopyGroup.Pi (n+1) (HomotopyFiber f y) (basepoint f y x h))]
    [Subsingleton (HomotopyGroup.Pi n (HomotopyFiber f y) (basepoint f y x h))] :
    Function.Bijective (piMap n f h) := piMap_bijective_of_subsingleton_fiber f y x h n
example
    [Subsingleton (HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x h))]
    [Subsingleton (HomotopyGroup.Pi 0 (HomotopyFiber f y) (basepoint f y x h))] :
    Function.Bijective (piMap 0 f h) := piMap_bijective_of_subsingleton_fiber f y x h 0
end Contractibility
