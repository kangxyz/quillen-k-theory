/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.Topology.HomotopyGroups.BasedMapNaturality
/-! # Original corrected maps under a based homotopy square -/
noncomputable section
universe u v u' v'
open Quillen
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']
example
    (f : C(X, Y)) (g : C(X', Y')) (a : C(X, X')) (b : C(Y, Y'))
    (H : (b.comp f).Homotopy (g.comp a))
    (x : X) (x' : X') (y : Y) (y' : Y')
    (pf : Path (f x) y) (pg : Path (g x') y')
    (pa : Path (a x) x') (pb : Path (b y) y')
    (hpath : ((pf.map b.continuous).trans pb).Homotopic
      ((H.evalAt x).trans ((pa.map g.continuous).trans pg)))
    (n : ℕ) (α : HomotopyGroup.Pi n X x) :
    pathTransport pb n (homotopyGroupMap b rfl
      (pathTransport pf n (homotopyGroupMap f rfl α))) =
    pathTransport pg n (homotopyGroupMap g rfl
      (pathTransport pa n (homotopyGroupMap a rfl α))) :=
  homotopyGroupMap_based_square f g a b H x x' y y' pf pg pa pb hpath n α
