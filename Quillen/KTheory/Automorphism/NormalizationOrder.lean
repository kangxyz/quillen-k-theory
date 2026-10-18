/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Automorphism.PositiveNormalization
public import Quillen.KTheory.SpaceAction

/-!
# Order of the original loop normalization

The corrected class of inverse-first right normalization is the object-loop
transport of the corrected positive normalization. A continuous cut rotation
in the actual free-path space supplies this action formula. Its two endpoint
unit homotopies retain the original cancellation and reversal caps; commutativity
of the loop-space fundamental group is used only for correction paths.

Triviality of the object-loop action gives equality of these classes. The original
Quillen space supplies that hypothesis through its actual Q/S and iterated-S maps.
This module does not identify a localized-completion representative with either
normalization; that remaining marking comparison belongs to its defining map.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u v w
namespace Quillen.Automorphism
variable {X : Type u} [TopologicalSpace X] {x : X}

private def correctedClass {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z) (γ : Path (f z) (Path.refl x))
    (a : HomotopyGroup.Pi 1 Z z) : HomotopyGroup.Pi 2 X x :=
  (loopShiftMulEquiv 0).symm
    (pathTransportMulEquiv γ 0 (piMap 0 f rfl a))

private def componentClass {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z) (a : HomotopyGroup.Pi 1 Z z) :=
  loopComponentToPiTwo (f z)
    (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a))

private def normalizationNullHomotopy {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z) (γ : Path (f z) (Path.refl x)) :
    (rightNormalizedLoopMap f z).Homotopy f := by
  let g : C(Z, Path x x) := ⟨fun w => (f w).trans (Path.refl x),
    Path.continuous_trans.comp (f.continuous.prodMk continuous_const)⟩
  let H : (rightNormalizedLoopMap f z).Homotopy g := {
    toFun := fun a => (f a.2).trans (γ a.1).symm
    continuous_toFun := Path.continuous_trans.comp
      ((f.continuous.comp continuous_snd).prodMk
        (Path.continuous_symm.comp (γ.continuous.comp continuous_fst)))
    map_zero_left := by intro w; change (f w).trans (γ 0).symm = _; rw [γ.source]; rfl
    map_one_left := by intro w; change (f w).trans (γ 1).symm = _; rw [γ.target]; rfl }
  let K : g.Homotopy f := {
    toFun := fun a => Path.delayReflRight a.1 (f a.2)
    continuous_toFun := Path.continuous_delayReflRight.comp
      (continuous_fst.prodMk (f.continuous.comp continuous_snd))
    map_zero_left := fun w => Path.delayReflRight_zero (f w)
    map_one_left := fun w => Path.delayReflRight_one (f w) }
  exact H.trans K

private theorem componentClass_eq_corrected {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z) (γ : Path (f z) (Path.refl x))
    (a : HomotopyGroup.Pi 1 Z z) : componentClass f z a = correctedClass f z γ a := by
  have h := DFunLike.congr_fun (piOne_homotopy_corrected
    (normalizationNullHomotopy f z γ) (rightNormalizationPath f z) γ
    (loopComponent_piOne_mul_comm (Path.refl x))) a
  exact (rightNormalization_formula f z a).symm.trans
    (congrArg (loopShiftMulEquiv 0).symm h)

private theorem componentClass_eq_corrected_of_homotopy
    {Z : Type v} [TopologicalSpace Z] {f g : C(Z, Path x x)}
    (H : f.Homotopy g) (z : Z) (γ : Path (g z) (Path.refl x))
    (a : HomotopyGroup.Pi 1 Z z) : componentClass f z a = correctedClass g z γ a := by
  let δ := (H.evalAt z).trans γ
  have h := DFunLike.congr_fun (piOne_homotopy_corrected H δ γ
    (loopComponent_piOne_mul_comm (Path.refl x))) a
  exact (componentClass_eq_corrected f z δ a).trans
    (congrArg (loopShiftMulEquiv 0).symm h)

private def cutHead (p : Path x x) (t : unitInterval) : Path x (p t) where
  toFun s := p (t * s)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

private def cutTail (p : Path x x) (t : unitInterval) : Path (p t) x where
  toFun s := p (unitInterval.symm (unitInterval.symm t * unitInterval.symm s))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

private def cutLoop (p q : Path x x) (t : unitInterval) : Path (p t) (p t) :=
  ((cutTail p t).trans q).trans (cutHead p t)

private theorem cutLoop_continuous (p : Path x x) :
    Continuous (fun z : (unitInterval × Path x x) × unitInterval =>
      cutLoop p z.1.2 z.1.1 z.2) := by
  have ht : Continuous (fun z : (unitInterval × Path x x) × unitInterval =>
      cutTail p z.1.1 z.2) := by
    change Continuous (fun z : (unitInterval × Path x x) × unitInterval =>
      p (unitInterval.symm (unitInterval.symm z.1.1 * unitInterval.symm z.2)))
    fun_prop
  have hq : Continuous (fun z : (unitInterval × Path x x) × unitInterval => z.1.2 z.2) := by
    fun_prop
  have hh : Continuous (fun z : (unitInterval × Path x x) × unitInterval =>
      cutHead p z.1.1 z.2) := by
    change Continuous (fun z : (unitInterval × Path x x) × unitInterval => p (z.1.1 * z.2))
    fun_prop
  exact Path.trans_continuous_family
    (fun z : unitInterval × Path x x => (cutTail p z.1).trans z.2)
    (Path.trans_continuous_family (fun z : unitInterval × Path x x => cutTail p z.1) ht
      (fun z : unitInterval × Path x x => z.2) hq)
    (fun z : unitInterval × Path x x => cutHead p z.1) hh

private def cutLoopMap (p : Path x x) : C((unitInterval × Path x x) × unitInterval, X) :=
  ⟨fun z => cutLoop p z.1.2 z.1.1 z.2, cutLoop_continuous p⟩

/-- Moving the cut through p gives loops in the actual free-path space,
whose basepoint is the whole displayed path p. -/
private def cutFamily (p : Path x x) :
    C(Path x x, Path p.toContinuousMap p.toContinuousMap) where
  toFun (q : Path x x) := {
    toFun (s : unitInterval) := (cutLoopMap p).comp
      ⟨fun t : unitInterval => ((t, q), s), by fun_prop⟩
    continuous_toFun := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun st : unitInterval × unitInterval => cutLoopMap p ((st.2, q), st.1))
      exact (cutLoopMap p).continuous.comp (by fun_prop)
    source' := by ext t; exact (cutLoop p q t).source
    target' := by ext t; exact (cutLoop p q t).target }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (Path x x × unitInterval) × unitInterval =>
      cutLoopMap p ((z.2, z.1.1), z.1.2))
    exact (cutLoopMap p).continuous.comp (by fun_prop)

private theorem cutFamily_zero (p q : Path x x) :
    basedLoopMap (freePathEvaluation X 0) p.source (cutFamily p q) =
      (p.trans q).trans (Path.refl x) := by
  ext s
  change cutLoop p q 0 s = _
  simp [cutLoop, cutHead, cutTail, Path.trans_apply]

private theorem cutFamily_one (p q : Path x x) :
    basedLoopMap (freePathEvaluation X 1) p.target (cutFamily p q) =
      ((Path.refl x).trans q).trans p := by
  ext s
  change cutLoop p q 1 s = _
  simp [cutLoop, cutHead, cutTail, Path.trans_apply]

private def cutCore {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z) :
    C(Z, Path (f z).toContinuousMap (f z).toContinuousMap) :=
  (cutFamily (f z)).comp (loopReversal.comp f)

private def cutZero {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z) : C(Z, Path x x) :=
  (basedLoopMap (freePathEvaluation X 0) (f z).source).comp (cutCore f z)

private def cutOne {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z) : C(Z, Path x x) :=
  (basedLoopMap (freePathEvaluation X 1) (f z).target).comp (cutCore f z)

private def cutZeroHomotopy {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z) :
    (cutZero f z).Homotopy (positiveNormalizedLoopMap f z) where
  toFun a := Path.delayReflRight a.1 ((f z).trans (f a.2).symm)
  continuous_toFun := Path.continuous_delayReflRight.comp
    (continuous_fst.prodMk (Path.continuous_trans.comp
      (continuous_const.prodMk (Path.continuous_symm.comp (f.continuous.comp continuous_snd)))))
  map_zero_left w := by
    rw [Path.delayReflRight_zero]
    exact (cutFamily_zero (f z) (f w).symm).symm
  map_one_left w := by
    rw [Path.delayReflRight_one]
    change (f z).trans (f w).symm = ((f w).trans (f z).symm).symm
    rw [Path.trans_symm, Path.symm_symm]

private def cutOneHomotopy {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z) :
    (cutOne f z).Homotopy (rightNormalizedLoopMap (loopReversal.comp f) z) where
  toFun a := (Path.delayReflLeft a.1 (f a.2).symm).trans (f z)
  continuous_toFun := Path.continuous_trans.comp
    ((Path.continuous_delayReflLeft.comp
      (continuous_fst.prodMk (Path.continuous_symm.comp (f.continuous.comp continuous_snd)))).prodMk
        continuous_const)
  map_zero_left w := by
    rw [Path.delayReflLeft_zero]
    exact (cutFamily_one (f z) (f w).symm).symm
  map_one_left w := by
    rw [Path.delayReflLeft_one]
    change (f w).symm.trans (f z) = (f w).symm.trans (f z).symm.symm
    rw [Path.symm_symm]

private theorem fundamentalMap_comp {A B D : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace D]
    (f : C(A, B)) (g : C(B, D)) (a : A) (c : FundamentalGroup A a) :
    FundamentalGroup.map g (f a) (FundamentalGroup.map f a c) =
      FundamentalGroup.map (g.comp f) a c := by
  obtain ⟨α, rfl⟩ := Path.Homotopic.Quotient.mk_surjective c
  rfl

private theorem componentClass_natural
    {Y : Type w} [TopologicalSpace Y] {y : Y}
    {Z : Type v} [TopologicalSpace Z]
    (g : C(X, Y)) (hg : g x = y) (f : C(Z, Path x x)) (z : Z)
    (a : HomotopyGroup.Pi 1 Z z) :
    homotopyGroupMap g hg (componentClass f z a) =
      componentClass ((basedLoopMap g hg).comp f) z a := by
  change piMap 1 g hg (loopComponentToPiTwo (f z)
    (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a))) = _
  rw [Cap.loopComponentToPiTwo_natural]
  change loopComponentToPiTwo (basedLoopMap g hg (f z))
    (FundamentalGroup.map (basedLoopMap g hg) (f z)
      (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a))) = _
  rw [fundamentalMap_comp]
  rfl

/-- The two original normalization orders differ by the action of the
actual object loop. Both displayed cancellation caps are retained. -/
theorem normalizationOrder_action {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z) (a : HomotopyGroup.Pi 1 Z z) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv (rightNormalizationPath (loopReversal.comp f) z) 0
        (piMap 0 (rightNormalizedLoopMap (loopReversal.comp f) z) rfl a)) =
      pathTransport (f z) 2
        ((loopShiftMulEquiv 0).symm
          (pathTransportMulEquiv (positiveNormalizationPath f z) 0
            (piMap 0 (positiveNormalizedLoopMap f z) rfl a))) := by
  let b := componentClass (cutCore f z) z a
  have ht := pathTransport_homotopyGroupMap_start (f z) 2 b
  have h0 : homotopyGroupMap (freePathEvaluation X 0) (f z).source b =
      correctedClass (positiveNormalizedLoopMap f z) z (positiveNormalizationPath f z) a := by
    exact (componentClass_natural (freePathEvaluation X 0) (f z).source (cutCore f z) z a).trans
      (componentClass_eq_corrected_of_homotopy (cutZeroHomotopy f z) z
        (positiveNormalizationPath f z) a)
  have h1 : homotopyGroupMap (freePathEvaluation X 1) (f z).target b =
      correctedClass (rightNormalizedLoopMap (loopReversal.comp f) z) z
        (rightNormalizationPath (loopReversal.comp f) z) a := by
    exact (componentClass_natural (freePathEvaluation X 1) (f z).target (cutCore f z) z a).trans
      (componentClass_eq_corrected_of_homotopy (cutOneHomotopy f z) z
        (rightNormalizationPath (loopReversal.comp f) z) a)
  rw [h0, h1] at ht
  exact ht.symm

/-- Triviality of the actual Pi-two object-loop action identifies the
original corrected classes, without asserting a global commutation homotopy. -/
theorem normalizationOrder_of_trivial_action {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z)
    (hp : ∀ b : HomotopyGroup.Pi 2 X x, pathTransport (f z) 2 b = b)
    (a : HomotopyGroup.Pi 1 Z z) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv (rightNormalizationPath (loopReversal.comp f) z) 0
        (piMap 0 (rightNormalizedLoopMap (loopReversal.comp f) z) rfl a)) =
      (loopShiftMulEquiv 0).symm
        (pathTransportMulEquiv (positiveNormalizationPath f z) 0
          (piMap 0 (positiveNormalizedLoopMap f z) rfl a)) :=
  (normalizationOrder_action f z a).trans (hp _)

open CategoryTheory.Limits CategoryTheory.ExactCategory

/-- The original Quillen space supplies the required trivial action. -/
theorem normalizationOrder_qSpace
    {C : Type u} [Category.{w} C] [Preadditive C] [HasFiniteBiproducts C]
    (E : ExactStructure C) {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path E.kBasepoint E.kBasepoint)) (z : Z)
    (a : HomotopyGroup.Pi 1 Z z) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv (rightNormalizationPath (loopReversal.comp f) z) 0
        (piMap 0 (rightNormalizedLoopMap (loopReversal.comp f) z) rfl a)) =
      (loopShiftMulEquiv 0).symm
        (pathTransportMulEquiv (positiveNormalizationPath f z) 0
          (piMap 0 (positiveNormalizedLoopMap f z) rfl a)) :=
  normalizationOrder_of_trivial_action f z (qSpace_piTwo_pathTransport_loop E (f z)) a

end Quillen.Automorphism
