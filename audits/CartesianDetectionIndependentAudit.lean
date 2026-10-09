import Lean.Util.CollectAxioms
import Quillen.Topology.HomotopyFiber.CartesianDetection

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == `Quillen.Topology.HomotopyFiber.CartesianDetection do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}"
  unless count == 25 do throwError "Expected exactly 25 declarations, found {count}"
  logInfo m!"Audited all {count} CartesianDetection declarations."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Quillen Quillen.HomotopyPullback
open scoped Topology unitInterval
universe u
variable {X Y B C : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B] [TopologicalSpace C]
  (f : C(X, B)) (g : C(Y, C)) (a : C(X, Y)) (b : C(B, C))
  (sq : g.comp a = b.comp f) (z : B)
example (p : HomotopyFiber f z) : (transitionFiber f g a b sq z p).1.1 = a p.1.1 := rfl
example (p : HomotopyFiber f z) :
    (transitionFiber f g a b sq z p).1.2 = b.comp p.1.2 := rfl
example (p : HomotopyFiber f z) :
    (comparisonFiber f g a b sq z p).1.2 = p.1.2 := rfl
example (p : HomotopyFiber f z) (t s : unitInterval) :
    (comparisonFiberHomotopy f g a b sq z (t,p)).1.1.1.2.2 s = b (p.1.2 (t*s)) := rfl
example (p : HomotopyFiber f z) (t s : unitInterval) :
    (comparisonFiberHomotopy f g a b sq z (t,p)).1.2 s =
      p.1.2 (unitInterval.symm (unitInterval.symm t * unitInterval.symm s)) := rfl
example (x : X) (hx : f x = z) (t : unitInterval) :
    comparisonFiberHomotopy f g a b sq z (t, HomotopyFiber.basepoint f z x hx) =
      comparisonFiber f g a b sq z (HomotopyFiber.basepoint f z x hx) :=
  comparisonFiberHomotopy_fixed f g a b sq z x hx t
example (x : X) (hx : f x = z) (n : ℕ)
    (h : Function.Bijective (homotopyGroupMap (N := Fin n)
      (transitionFiber f g a b sq z) (x := HomotopyFiber.basepoint f z x hx) rfl)) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (comparisonFiber f g a b sq z) (x := HomotopyFiber.basepoint f z x hx) rfl) :=
  comparisonFiber_bijective f g a b sq z x hx n h
example [PathConnectedSpace X] [PathConnectedSpace B]
    [PathConnectedSpace (HomotopyFiber g (b z))] (x : X) (hx : f x = z)
    (h : ∀ n : ℕ, Function.Bijective (homotopyGroupMap (N := Fin n)
      (transitionFiber f g a b sq z) (x := HomotopyFiber.basepoint f z x hx) rfl))
    (x' : X) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (comparison g b f a sq) (x := x') rfl) :=
  comparison_bijective_of_fiberMap f g a b sq z x hx h x' n
example [PathConnectedSpace X] [PathConnectedSpace B]
    [PathConnectedSpace (HomotopyFiber g (b z))] (x : X) (hx : f x = z)
    (h : ∀ n : ℕ, Function.Bijective (homotopyGroupMap (N := Fin n)
      (transitionFiber f g a b sq z) (x := HomotopyFiber.basepoint f z x hx) rfl)) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (comparison g b f a sq) (x := x) rfl) :=
  comparison_bijective_of_fiberMap f g a b sq z x hx h x 0

example (p : HomotopyFiber f z) :
    comparisonFiberHomotopy f g a b sq z (0, p) = comparisonFiber f g a b sq z p :=
  (comparisonFiberHomotopy f g a b sq z).map_zero_left p
example (p : HomotopyFiber f z) :
    comparisonFiberHomotopy f g a b sq z (1, p) =
      baseFiberComparison g b z (transitionFiber f g a b sq z p) :=
  (comparisonFiberHomotopy f g a b sq z).map_one_left p
example (p : HomotopyFiber f z) (t : unitInterval) :
    (comparisonFiberHomotopy f g a b sq z (t,p)).1.1.1.1 = p.1.2 t := rfl
example (p : HomotopyFiber f z) :
    (comparisonFiber f g a b sq z p).1.1 = comparison g b f a sq p.1.1 := rfl
example (x : X) (hx : f x = z)
    (h : Function.Bijective (homotopyGroupMap (N := Fin 0)
      (transitionFiber f g a b sq z) (x := HomotopyFiber.basepoint f z x hx) rfl)) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (comparisonFiber f g a b sq z) (x := HomotopyFiber.basepoint f z x hx) rfl) :=
  comparisonFiber_bijective f g a b sq z x hx 0 h
example [PathConnectedSpace B] [PathConnectedSpace (HomotopyFiber g (b z))] :
    PathConnectedSpace (HomotopyPullback g b) := pathConnectedSpace g b z
