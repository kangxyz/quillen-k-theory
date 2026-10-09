import Quillen.Library
import Quillen.Topology.HomotopyFiber.WeakSourceEquivalence

noncomputable section
open Quillen
open scoped Topology
universe u
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
variable (f : C(X, B)) (g : C(Y, B)) (m : C(X,Y)) (sq : g.comp m = f)
    (b : B) (hm : IsWeakHomotopyEquivalence m)
example : IsWeakHomotopyEquivalence (HomotopyFiber.mapOver f g m sq b) :=
  HomotopyFiber.mapOver_isWeakHomotopyEquivalence f g m sq b hm
example (z : HomotopyFiber f b) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (HomotopyFiber.mapOver f g m sq b) (x := z) rfl) :=
  HomotopyFiber.homotopyGroupMap_mapOver_bijective f g m sq b hm z 0
example (z : HomotopyFiber f b) : (HomotopyFiber.mapOver f g m sq b z).1.2 = z.1.2 := rfl
