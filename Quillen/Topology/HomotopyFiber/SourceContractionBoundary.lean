/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.HomotopyFiber.SourceContraction
public import Quillen.Topology.HomotopyGroups.PathTransportFundamentalGroup
public import Quillen.Topology.HomotopyGroups.PathTransportComposition
public import Quillen.Topology.HomotopyFiber.LES

/-!
# The original connecting map from a displayed source contraction

A contraction of the source coordinate of a given fiber map supplies the original
contracted path difference. The source slide, prefix change and cancellation
construct a forward homotopy from that normalized loop family to the original
fiber map. No contraction of the whole source space is required.

With the given basedness and an actual normalization cap, commutativity of the
fiber's fundamental group removes only correction-path dependence. The resulting
formula computes the original degree-zero connecting homomorphism on the displayed
corrected loop class. In the Serre application the canonical comparison with K-zero
supplies that commutativity; identifying a particular automorphism cube still
requires its actual categorical diagram and full path-family comparison.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open scoped Topology unitInterval
namespace Quillen.HomotopyFiber
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : C(X, Y)) (y : Y) (h : C(Z, HomotopyFiber f y)) (e : X)
  (H : ((projection f y).comp h).Homotopy (ContinuousMap.const Z e))

/-- Retain the full stored paths while comparing with the normalized contracted path map. -/
def contractionForwardHomotopy (z₀ : Z) :
    ((loopPrefix f (h z₀).val.1 y (toPath f y (h z₀))).comp
      (contractedDifference f y h e H z₀)).Homotopy h := by
  let a := contractedPathMap f y h e H
  let d := contractedDifference f y h e H z₀
  let K := contractionFiberHomotopy f y h e H
  let q := K.evalAt z₀
  have P : ((loopPrefix f e y (a z₀)).comp d).Homotopy
      ((constantSourcePathMap f y e).comp a) :=
    (ContinuousMap.Homotopy.refl (constantSourcePathMap f y e)).comp
      ((prefixCancellation (c := y) (a z₀)).compContinuousMap a)
  have Q : ((loopPrefix f (h z₀).val.1 y (toPath f y (h z₀))).comp d).Homotopy
      ((loopPrefix f e y (a z₀)).comp d) :=
    (loopPrefixPathHomotopy q).compContinuousMap d
  exact Q.trans (P.trans K.symm)

/-- The actual forward comparison retains a supplied normalization cap.
Commutativity is used only to remove correction-path dependence. -/
theorem contractionForward_piOne (z₀ : Z)
    (γ : Path (contractedDifference f y h e H z₀ z₀) (Path.refl y))
    (hc : ∀ a b : HomotopyGroup.Pi 1 (HomotopyFiber f y) (h z₀), a * b = b * a)
    (a : HomotopyGroup.Pi 1 Z z₀) :
    pathTransport (loopPrefixUnitPath f (h z₀).val.1 y (toPath f y (h z₀))) 1
      (homotopyGroupMap (loopPrefix f (h z₀).val.1 y (toPath f y (h z₀))) rfl
        (pathTransport γ 1 (homotopyGroupMap (contractedDifference f y h e H z₀) rfl a))) =
      homotopyGroupMap h rfl a := by
  let d := contractedDifference f y h e H z₀
  let P := loopPrefix f (h z₀).val.1 y (toPath f y (h z₀))
  let p := loopPrefixUnitPath f (h z₀).val.1 y (toPath f y (h z₀))
  let θ := (γ.map P.continuous).trans p
  have hh := DFunLike.congr_fun (piOne_homotopy_corrected
    (contractionForwardHomotopy f y h e H z₀) θ (Path.refl (h z₀)) hc) a
  change pathTransport θ 1 (homotopyGroupMap (P.comp d) rfl a) =
    pathTransport (Path.refl (h z₀)) 1 (homotopyGroupMap h rfl a) at hh
  rw [pathTransport_refl, Equiv.refl_apply] at hh
  rw [pathTransport_trans] at hh
  rw [homotopyGroupMap_comp d rfl P rfl a, pathTransport_naturality] at hh
  exact hh

/-- At the original constant-path fiber point, delete the constant prefix jointly. -/
private def basepointPrefixHomotopy (x : X) (hx : f x = y) :
    (loopPrefix f x y (toPath f y (basepoint f y x hx))).Homotopy
      (loopInclusion f y x hx) where
  toFun z := loopInclusion f y x hx (Path.delayReflLeft z.1 z.2)
  continuous_toFun := (loopInclusion f y x hx).continuous.comp Path.continuous_delayReflLeft
  map_zero_left γ := by
    rw [Path.delayReflLeft_zero]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      change ((Path.refl y).trans γ) t = ((toPath f y (basepoint f y x hx)).trans γ) t
      simp only [Path.trans_apply]
      split_ifs <;> rfl
  map_one_left γ := by rw [Path.delayReflLeft_one]

/-- The corrected prefix at the actual basepoint is the original loop inclusion. -/
private theorem basepointPrefix_piOne (x : X) (hx : f x = y)
    (hc : ∀ a b : HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x hx), a * b = b * a)
    (a : HomotopyGroup.Pi 1 (Path y y) (Path.refl y)) :
    pathTransport (loopPrefixUnitPath f x y (toPath f y (basepoint f y x hx))) 1
      (homotopyGroupMap (loopPrefix f x y (toPath f y (basepoint f y x hx))) rfl a) =
      homotopyGroupMap (loopInclusion f y x hx) (loopInclusion_refl f y x hx) a := by
  have hh := DFunLike.congr_fun (piOne_homotopy_corrected
    (basepointPrefixHomotopy f y x hx)
    (loopPrefixUnitPath f x y (toPath f y (basepoint f y x hx)))
    (Path.refl (basepoint f y x hx)) hc) a
  change pathTransport (loopPrefixUnitPath f x y (toPath f y (basepoint f y x hx))) 1
      (homotopyGroupMap (loopPrefix f x y (toPath f y (basepoint f y x hx))) rfl a) =
    pathTransport (Path.refl (basepoint f y x hx)) 1
      (homotopyGroupMap (loopInclusion f y x hx) rfl a) at hh
  simpa only [pathTransport_refl, Equiv.refl_apply] using hh

private theorem transport_eq_map {T W : Type*} [TopologicalSpace T] [TopologicalSpace W]
    (k : C(T, W)) (t : T) (b : W) (hk : k t = b) (a : HomotopyGroup.Pi 1 T t) :
    pathTransport ((Path.refl (k t)).cast rfl hk.symm) 1 (homotopyGroupMap k rfl a) =
      homotopyGroupMap k hk a := by
  subst b
  simp only [Path.cast_rfl_rfl, pathTransport_refl, Equiv.refl_apply]

/-- A displayed source contraction computes the original connecting map of its
actual normalized path difference. No global contraction or inverse comparison is assumed. -/
theorem connecting_contractedDifference (z₀ : Z) (x : X) (hx : f x = y)
    (hb : h z₀ = basepoint f y x hx)
    (γ : Path (contractedDifference f y h e H z₀ z₀) (Path.refl y))
    (hc : ∀ a b : HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x hx), a * b = b * a)
    (a : HomotopyGroup.Pi 1 Z z₀) :
    connectingHom f y x hx 0
      ((loopShiftMulEquiv 0).symm
        (pathTransport γ 1 (homotopyGroupMap (contractedDifference f y h e H z₀) rfl a))) =
      homotopyGroupMap h hb a := by
  let b := pathTransport γ 1 (homotopyGroupMap (contractedDifference f y h e H z₀) rfl a)
  let κ : Path (h z₀) (basepoint f y x hx) := (Path.refl (h z₀)).cast rfl hb.symm
  have hcz (c d : HomotopyGroup.Pi 1 (HomotopyFiber f y) (h z₀)) : c * d = d * c := by
    apply (pathTransportMulEquiv κ 0).injective
    simp only [map_mul]
    exact hc _ _
  have hh := congrArg (pathTransport κ 1)
    (contractionForward_piOne f y h e H z₀ γ hcz a)
  have ht := loopPrefix_pathTransport_pi κ 1 b
  have hm := transport_eq_map h z₀ (basepoint f y x hx) hb a
  have hb' := ht.symm.trans hh
  change pathTransport (loopPrefixUnitPath f x y (toPath f y (basepoint f y x hx))) 1
      (homotopyGroupMap (loopPrefix f x y (toPath f y (basepoint f y x hx))) rfl b) =
    pathTransport κ 1 (homotopyGroupMap h rfl a) at hb'
  have hfwd := (basepointPrefix_piOne f y x hx hc b).symm.trans (hb'.trans hm)
  change homotopyGroupMap (loopInclusion f y x hx) (loopInclusion_refl f y x hx)
    (loopShiftMulEquiv 0 ((loopShiftMulEquiv 0).symm b)) = _
  rw [MulEquiv.apply_symm_apply]
  exact hfwd

end Quillen.HomotopyFiber
