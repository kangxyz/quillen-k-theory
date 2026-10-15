/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.CommonUniverseChains
public import Quillen.Topology.PlusConstruction.Basic

/-! # Exact based transport of the original plus certificate to a common universe

The original map, path and subgroup are transported by the
actual ULift homeomorphisms. The coefficient hypothesis already ranges over
the common universe; no enlargement from smaller coefficients is asserted.
-/
@[expose] public section

open Quillen.LocalCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u v w
namespace Quillen.PlusConstruction.CommonUniverse
open LocalCoefficients

variable {X : Type u} [TopologicalSpace X]

/-- The original based Pi-one map of ULift.up is an actual multiplicative equivalence. -/
def piEquiv (x : X) :
    HomotopyGroup.Pi 1 X x ≃* HomotopyGroup.Pi 1 (ULift.{w} X) (ULift.up x) where
  toFun := piMap 0 (UniverseLift.up X) rfl
  invFun := piMap 0 (UniverseLift.down X) rfl
  left_inv a := by
    change homotopyGroupMap (UniverseLift.down X) rfl
      (homotopyGroupMap (UniverseLift.up X) rfl a) = a
    rw [← homotopyGroupMap_comp]
    exact homotopyGroupMap_id a
  right_inv a := by
    change homotopyGroupMap (UniverseLift.up X) rfl
      (homotopyGroupMap (UniverseLift.down X) rfl a) = a
    rw [← homotopyGroupMap_comp]
    exact homotopyGroupMap_id a
  map_mul' := (piMap 0 (UniverseLift.up X) rfl).map_mul

/-- The forward Pi-one equivalence is exactly the original induced continuous-map homomorphism. -/
@[simp] theorem piEquiv_apply (x : X) (a : HomotopyGroup.Pi 1 X x) :
    piEquiv.{u, w} x a = piMap 0 (UniverseLift.up.{u, w} X) rfl a := rfl

/-- Transport the actual subgroup, rather than choosing an isomorphic replacement. -/
def liftSubgroup {x : X} (N : Subgroup (HomotopyGroup.Pi 1 X x)) :
    Subgroup (HomotopyGroup.Pi 1 (ULift.{w} X) (ULift.up x)) :=
  N.map (piEquiv.{u, w} x).toMonoidHom

variable {Y : Type v} [TopologicalSpace Y]
  (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y)

/-- The supplied under-basepoint track is mapped by the literal inverse projection homeomorphism. -/
def liftPath :
    Path (CommonUniverseChains.liftMap.{u, v, w} f (ULift.up x))
      (ULift.up y : ULift.{max u v w} Y) :=
  γ.map continuous_uliftUp

/-- Every time of the specified track is retained. -/
@[simp] theorem liftPath_apply (t : unitInterval) :
    liftPath.{u, v, w} f γ t = ULift.up (γ t) := rfl

/-- Projecting the transported track returns the original path, including its endpoints. -/
theorem liftPath_down :
    (liftPath.{u, v, w} f γ).map continuous_uliftDown = γ := by
  ext t
  rfl

/-- The complete based Pi-one square uses the originally specified path transport. -/
theorem basedPiOneMap_lift_apply (a : HomotopyGroup.Pi 1 X x) :
    basedPiOneMap (CommonUniverseChains.liftMap.{u, v, w} f)
        (liftPath f γ) (piEquiv.{u, max u v w} x a) =
      piEquiv.{v, max u v w} y (basedPiOneMap f γ a) := by
  change pathTransport (γ.map continuous_uliftUp) 1
      (homotopyGroupMap (CommonUniverseChains.liftMap.{u, v, w} f) rfl
        (homotopyGroupMap (UniverseLift.up X) rfl a)) =
    homotopyGroupMap (UniverseLift.up Y) rfl
      (pathTransport γ 1 (homotopyGroupMap f rfl a))
  have hm : homotopyGroupMap (CommonUniverseChains.liftMap.{u, v, w} f) rfl
      (homotopyGroupMap (UniverseLift.up X) rfl a) =
        homotopyGroupMap (UniverseLift.up Y) rfl (homotopyGroupMap f rfl a) := by
    refine Quotient.inductionOn a (fun _ => ?_)
    rfl
  rw [hm]
  exact pathTransport_naturality (UniverseLift.up Y) γ 1 (homotopyGroupMap f rfl a)

/-- The based square is an equality of the original nonabelian group homomorphisms. -/
theorem basedPiOneMap_square :
    (basedPiOneMap (CommonUniverseChains.liftMap.{u, v, w} f) (liftPath f γ)).comp
        (piEquiv.{u, max u v w} x).toMonoidHom =
      (piEquiv.{v, max u v w} y).toMonoidHom.comp (basedPiOneMap f γ) := by
  ext a
  exact basedPiOneMap_lift_apply f γ a

/-- Surjectivity transfers through the displayed based square. -/
theorem basedPiOneMap_lift_surjective (h : Function.Surjective (basedPiOneMap f γ)) :
    Function.Surjective
      (basedPiOneMap (CommonUniverseChains.liftMap.{u, v, w} f) (liftPath f γ)) := by
  intro b
  obtain ⟨b, rfl⟩ := (piEquiv.{v, max u v w} y).surjective b
  obtain ⟨a, rfl⟩ := h b
  exact ⟨piEquiv.{u, max u v w} x a, basedPiOneMap_lift_apply f γ a⟩

/-- The kernel is the image of the original kernel under the specified Pi-one equivalence. -/
theorem kernel_lift :
    (basedPiOneMap (CommonUniverseChains.liftMap.{u, v, w} f) (liftPath f γ)).ker =
      liftSubgroup.{u, max u v w} (basedPiOneMap f γ).ker := by
  ext b
  obtain ⟨a, rfl⟩ := (piEquiv.{u, max u v w} x).surjective b
  change _ ↔ piEquiv.{u, max u v w} x a ∈
    (basedPiOneMap f γ).ker.map (piEquiv.{u, max u v w} x).toMonoidHom
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  change basedPiOneMap (CommonUniverseChains.liftMap.{u, v, w} f)
      (liftPath f γ) (piEquiv.{u, max u v w} x a) = 1 ↔ basedPiOneMap f γ a = 1
  rw [basedPiOneMap_lift_apply]
  constructor
  · intro h
    apply (piEquiv.{v, max u v w} y).injective
    simpa only [map_one] using h
  · intro h
    rw [h, map_one]

/-- The common-universe certificate retains the transported original map, path and subgroup. -/
theorem isPlusConstruction (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (h : IsPlusConstruction.{u, v, max u v w} f γ N) :
    IsPlusConstruction.{max u v w, max u v w, max u v w}
      (CommonUniverseChains.liftMap.{u, v, w} f) (liftPath f γ)
      (liftSubgroup.{u, max u v w} N) := by
  let := h.sourcePathConnected
  let := h.targetPathConnected
  let := h.perfect
  exact {
    sourcePathConnected := Homeomorph.ulift.symm.pathConnectedSpace
    targetPathConnected := Homeomorph.ulift.symm.pathConnectedSpace
    perfect := Group.IsPerfect.map (piEquiv.{u, max u v w} x).toMonoidHom
    surjective := basedPiOneMap_lift_surjective f γ h.surjective
    kernelEq := by rw [kernel_lift, h.kernelEq]
    localCoefficients := CommonUniverseChains.all_localCoefficients_liftMap f h.localCoefficients }

/-- Removing the two actual spatial lifts recovers exactly the original forward map. -/
theorem forward_down :
    (UniverseLift.down Y).comp
      ((CommonUniverseChains.liftMap.{u, v, w} f).comp (UniverseLift.up X)) = f := by
  ext z
  rfl

end Quillen.PlusConstruction.CommonUniverse
