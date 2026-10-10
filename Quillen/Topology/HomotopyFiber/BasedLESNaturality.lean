/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.HomotopyFiber.LESNaturality
public import Quillen.Topology.HomotopyFiber.BasedSquareMap

/-!
# Original connecting naturality at specified target basepoints

Both given basepoint equalities are retained by the actual fiber map.
The full original connecting homomorphisms commute.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open scoped Simplicial Topology
universe u v
namespace Quillen.HomotopyFiber
section Based
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] {f : C(X, A)} {g : C(Y, B)}
    (p : C(X, Y)) (q : C(A, B)) (sq : q.comp f = g.comp p)
    (x : X) (a : A) (y : Y) (b : B) (h : f x = a) (h' : g y = b)
    (hx : p x = y) (ha : q a = b)

include hx in
lemma mapAt_basepoint :
    mapAt p q sq a b ha (basepoint f a x h) = basepoint g b y h' := by
  apply Subtype.ext
  apply Prod.ext hx
  exact ContinuousMap.ext (fun _ => ha)

lemma connectingHom_mapAt_natural (n : ℕ) :
    (piMap n (mapAt p q sq a b ha) (mapAt_basepoint p q sq x a y b h h' hx ha)).comp
      (connectingHom f a x h n) =
    (connectingHom g b y h' n).comp (piMap (n+1) q ha) := by
  subst y
  subst b
  exact connectingHom_natural p q sq x a h n
end Based
end Quillen.HomotopyFiber
