/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.HomotopyFiber.FiniteTargetDetection

/-! # Finite source detection from the original fiber ladder

The original source in degree n+2 is detected using precisely the surrounding
positive degrees of the target and actual fiber map. All specified points are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Quillen.HomotopyFiber
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]
  {f : C(X, A)} {g : C(Y, B)} (p : C(X, Y)) (q : C(A, B))
  (sq : q.comp f = g.comp p) (x : X) (a : A) (h : f x = a)

/-- Four exact neighboring maps detect the source in degree n+2. -/
theorem piMap_source_bijective_of_fiberMap (n : ℕ)
    (hqhi : Function.Surjective (piMap (n + 2) q (x := a) rfl))
    (hfhi : Function.Bijective (piMap (n + 1) (map p q sq a)
      (map_basepoint p q sq x a h)))
    (hqlo : Function.Bijective (piMap (n + 1) q (x := a) rfl))
    (hflo : Function.Injective (piMap n (map p q sq a)
      (map_basepoint p q sq x a h))) :
    Function.Bijective (piMap (n + 1) p (x := x) rfl) := by
  let h' : g (p x) = q a :=
    (ContinuousMap.congr_fun sq x).symm.trans (congrArg q h)
  refine MonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (connectingHom f a x h (n + 1))
    (piMap (n + 1) (projection f a) (projection_basepoint f a x h))
    (piMap (n + 1) f h) (connectingHom f a x h n)
    (connectingHom g (q a) (p x) h' (n + 1))
    (piMap (n + 1) (projection g (q a)) (projection_basepoint g (q a) (p x) h'))
    (piMap (n + 1) g h') (connectingHom g (q a) (p x) h' n)
    (piMap (n + 2) q rfl)
    (piMap (n + 1) (map p q sq a) (map_basepoint p q sq x a h))
    (piMap (n + 1) p rfl) (piMap (n + 1) q rfl)
    (piMap n (map p q sq a) (map_basepoint p q sq x a h))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hqhi hfhi hqlo hflo
  · exact (connectingHom_natural p q sq x a h (n + 1)).symm
  · exact (projectionHom_natural p q sq x a h (n + 1)).symm
  · exact (originalHom_natural p q sq x a h (n + 1)).symm
  · exact (connectingHom_natural p q sq x a h n).symm
  · exact MonoidHom.mulExact_iff.mpr (range_connectingHom_eq_ker_projection f a x h (n + 1)).symm
  · exact MonoidHom.mulExact_iff.mpr (piMap_range_projection_eq_ker f a x h (n + 1)).symm
  · exact MonoidHom.mulExact_iff.mpr (range_piMap_eq_ker_connectingHom f a x h n).symm
  · exact MonoidHom.mulExact_iff.mpr
      (range_connectingHom_eq_ker_projection g (q a) (p x) h' (n + 1)).symm
  · exact MonoidHom.mulExact_iff.mpr
      (piMap_range_projection_eq_ker g (q a) (p x) h' (n + 1)).symm
  · exact MonoidHom.mulExact_iff.mpr (range_piMap_eq_ker_connectingHom g (q a) (p x) h' n).symm

/-- The finite source ladder retains both displayed target points. -/
theorem piMap_source_bijective_of_basedFiberMap (y : Y) (b : B)
    (h' : g y = b) (hx : p x = y) (ha : q a = b) (n : ℕ)
    (hqhi : Function.Surjective (piMap (n + 2) q ha))
    (hfhi : Function.Bijective (piMap (n + 1) (mapAt p q sq a b ha)
      (mapAt_basepoint p q sq x a y b h h' hx ha)))
    (hqlo : Function.Bijective (piMap (n + 1) q ha))
    (hflo : Function.Injective (piMap n (mapAt p q sq a b ha)
      (mapAt_basepoint p q sq x a y b h h' hx ha))) :
    Function.Bijective (piMap (n + 1) p hx) := by
  subst y
  subst b
  exact piMap_source_bijective_of_fiberMap p q sq x a h n hqhi hfhi hqlo hflo

end Quillen.HomotopyFiber
