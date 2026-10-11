/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.TelescopePushout

/-!
# Strict interchange of the original telescope and reduced pushout

The reverse map first descends entire height-valued paths on the original pushout, then
evaluates telescope height. This proves continuity without assuming products preserve quotient
maps. Both inverses retain all three original generator types and both independent times.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Telescope
variable (A : ℕ → LoopPrespectrum.{u}) (a : ∀ i, A i ⟶ A (i + 1))
    (B : ℕ → LoopPrespectrum.{u}) (b : ∀ i, B i ⟶ B (i + 1))
    (C : ℕ → LoopPrespectrum.{u}) (c : ∀ i, C i ⟶ C (i + 1))
    (f : ∀ i, A i ⟶ B i) (g : ∀ i, A i ⟶ C i)
    (hf : ∀ i, f i ≫ b i = a i ≫ f (i + 1))
    (hg : ∀ i, g i ≫ c i = a i ≫ g (i + 1))

/-- The original stage pushout maps by its actual three telescope inclusions. -/
def pushoutStageMap (i : ℕ) : HomotopyPushout.prespectrum (f i) (g i) ⟶
    HomotopyPushout.prespectrum (map A a B b f hf) (map A a C c g hg) :=
  HomotopyPushout.map (f i) (g i) (map A a B b f hf) (map A a C c g hg)
    (inclusion A a i) (inclusion B b i) (inclusion C c i)
    (inclusion_map A a B b f hf i).symm (inclusion_map A a C c g hg i).symm

/-- Original left-target cylinders curried in telescope height. -/
def pushoutStageLeftFamily (k i : ℕ) : C((B i).space k,
    C(unitInterval, HomotopyPushout.Space (map A a B b f hf) (map A a C c g hg) k)) :=
  ContinuousMap.curry ⟨fun z => HomotopyPushout.left (map A a B b f hf) (map A a C c g hg) k
    (cylinder B b k i (z.2, z.1)), by fun_prop⟩

/-- Original right-target cylinders curried in telescope height. -/
def pushoutStageRightFamily (k i : ℕ) : C((C i).space k,
    C(unitInterval, HomotopyPushout.Space (map A a B b f hf) (map A a C c g hg) k)) :=
  ContinuousMap.curry ⟨fun z => HomotopyPushout.right (map A a B b f hf) (map A a C c g hg) k
    (cylinder C c k i (z.2, z.1)), by fun_prop⟩

/-- Original overlap cylinders curried in the independent telescope height. -/
def pushoutStageCylinderFamily (k i : ℕ) : C(unitInterval × (A i).space k,
    C(unitInterval, HomotopyPushout.Space (map A a B b f hf) (map A a C c g hg) k)) :=
  ContinuousMap.curry ⟨fun z => HomotopyPushout.cylinder (map A a B b f hf)
    (map A a C c g hg) k (z.1.1, cylinder A a k i (z.2, z.1.2)), by fun_prop⟩

/-- Descend the complete original telescope-height paths before evaluating their time. -/
def pushoutStageTrackFamily (k i : ℕ) : C((HomotopyPushout.prespectrum (f i) (g i)).space k,
    C(unitInterval, HomotopyPushout.Space (map A a B b f hf) (map A a C c g hg) k)) where
  toFun := Quot.lift (Sum.elim
    (Sum.elim (pushoutStageLeftFamily A a B b C c f g hf hg k i)
      (pushoutStageRightFamily A a B b C c f g hf hg k i))
    (pushoutStageCylinderFamily A a B b C c f g hf hg k i)) (by
      intro x y h
      cases h with
      | left x =>
        ext t
        exact HomotopyPushout.cylinder_zero (map A a B b f hf) (map A a C c g hg) k
          (cylinder A a k i (t, x))
      | right x =>
        ext t
        exact HomotopyPushout.cylinder_one (map A a B b f hf) (map A a C c g hg) k
          (cylinder A a k i (t, x))
      | base s =>
        ext t
        change HomotopyPushout.cylinder (map A a B b f hf) (map A a C c g hg) k
          (s, cylinder A a k i (t, (A i).point k)) =
          HomotopyPushout.left (map A a B b f hf) (map A a C c g hg) k
            (cylinder B b k i (t, (B i).point k))
        rw [cylinder_point, cylinder_point]
        exact HomotopyPushout.cylinder_point (map A a B b f hf) (map A a C c g hg) k s)
  continuous_toFun := continuous_quot_lift _
    (((pushoutStageLeftFamily A a B b C c f g hf hg k i).continuous.sumElim
      (pushoutStageRightFamily A a B b C c f g hf hg k i).continuous).sumElim
      (pushoutStageCylinderFamily A a B b C c f g hf hg k i).continuous)

/-- The literal original height cylinder moves the whole original stage pushout coherently. -/
def pushoutStageTrack (i : ℕ) :
    Homotopy (pushoutStageMap A a B b C c f g hf hg i)
      (pushoutTransition A a B b C c f g hf hg i ≫
        pushoutStageMap A a B b C c f g hf hg (i + 1)) where
  level k := ⟨fun z => pushoutStageTrackFamily A a B b C c f g hf hg k i z.2 z.1,
    (pushoutStageTrackFamily A a B b C c f g hf hg k i).uncurry.continuous.comp continuous_swap⟩
  at_zero k q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z <;> rfl
      | inr z => rfl
  at_one k q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl x =>
          change HomotopyPushout.left (map A a B b f hf) (map A a C c g hg) k
            (cylinder B b k i (1, x)) = _
          rw [cylinder_one]
          rfl
        | inr x =>
          change HomotopyPushout.right (map A a B b f hf) (map A a C c g hg) k
            (cylinder C c k i (1, x)) = _
          rw [cylinder_one]
          rfl
      | inr z =>
        change HomotopyPushout.cylinder (map A a B b f hf) (map A a C c g hg) k
          (z.1, cylinder A a k i (1, z.2)) = _
        rw [cylinder_one]
        rfl
  at_point k t := by
    change HomotopyPushout.left (map A a B b f hf) (map A a C c g hg) k
      (cylinder B b k i (t, (B i).point k)) = _
    rw [cylinder_point]
    rfl
  comm k _s q _t := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z <;> rfl
      | inr z => rfl

/-- Descend the original stage maps and their whole original height tracks. -/
def pushoutFromTelescope :
    prespectrum (fun i => HomotopyPushout.prespectrum (f i) (g i))
        (pushoutTransition A a B b C c f g hf hg) ⟶
      HomotopyPushout.prespectrum (map A a B b f hf) (map A a C c g hg) :=
  desc (fun i => HomotopyPushout.prespectrum (f i) (g i))
    (pushoutTransition A a B b C c f g hf hg)
    (pushoutStageMap A a B b C c f g hf hg) (pushoutStageTrack A a B b C c f g hf hg)

/-- The reverse map retains each original left target and its actual height. -/
theorem pushoutFromTelescope_left (k i : ℕ) (t : unitInterval) (x : (B i).space k) :
    (pushoutFromTelescope A a B b C c f g hf hg).map k
      (cylinder (fun i => HomotopyPushout.prespectrum (f i) (g i))
        (pushoutTransition A a B b C c f g hf hg) k i
        (t, HomotopyPushout.left (f i) (g i) k x)) =
      HomotopyPushout.left (map A a B b f hf) (map A a C c g hg) k
        (cylinder B b k i (t, x)) := rfl

/-- The reverse map retains each original right target and its actual height. -/
theorem pushoutFromTelescope_right (k i : ℕ) (t : unitInterval) (x : (C i).space k) :
    (pushoutFromTelescope A a B b C c f g hf hg).map k
      (cylinder (fun i => HomotopyPushout.prespectrum (f i) (g i))
        (pushoutTransition A a B b C c f g hf hg) k i
        (t, HomotopyPushout.right (f i) (g i) k x)) =
      HomotopyPushout.right (map A a B b f hf) (map A a C c g hg) k
        (cylinder C c k i (t, x)) := rfl

/-- The reverse map retains the independent original pushout time and telescope height. -/
theorem pushoutFromTelescope_cylinder (k i : ℕ) (s t : unitInterval) (x : (A i).space k) :
    (pushoutFromTelescope A a B b C c f g hf hg).map k
      (cylinder (fun i => HomotopyPushout.prespectrum (f i) (g i))
        (pushoutTransition A a B b C c f g hf hg) k i
        (t, HomotopyPushout.cylinder (f i) (g i) k (s, x))) =
      HomotopyPushout.cylinder (map A a B b f hf) (map A a C c g hg) k
        (s, cylinder A a k i (t, x)) := rfl

/-- Both actual descents are inverse on the original pushout of telescopes. -/
theorem pushoutToTelescope_comp_pushoutFromTelescope :
    pushoutToTelescope A a B b C c f g hf hg ≫
      pushoutFromTelescope A a B b C c f g hf hg =
        𝟙 (HomotopyPushout.prespectrum (map A a B b f hf) (map A a C c g hg)) := by
  apply HomotopyPushout.hom_ext
  · apply hom_ext; intros; rfl
  · apply hom_ext; intros; rfl
  · intro k s q
    induction q using Quot.inductionOn with
    | h z => rfl

/-- Both actual descents are inverse on the original telescope of stage pushouts. -/
theorem pushoutFromTelescope_comp_pushoutToTelescope :
    pushoutFromTelescope A a B b C c f g hf hg ≫
      pushoutToTelescope A a B b C c f g hf hg =
        𝟙 (prespectrum (fun i => HomotopyPushout.prespectrum (f i) (g i))
          (pushoutTransition A a B b C c f g hf hg)) := by
  apply hom_ext
  intro k i t q
  induction q using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z <;> rfl
    | inr z => rfl

/-- The original reduced pushout and telescope commute by an actual strict prespectrum iso. -/
def pushoutIso : HomotopyPushout.prespectrum (map A a B b f hf) (map A a C c g hg) ≅
    prespectrum (fun i => HomotopyPushout.prespectrum (f i) (g i))
      (pushoutTransition A a B b C c f g hf hg) where
  hom := pushoutToTelescope A a B b C c f g hf hg
  inv := pushoutFromTelescope A a B b C c f g hf hg
  hom_inv_id := pushoutToTelescope_comp_pushoutFromTelescope A a B b C c f g hf hg
  inv_hom_id := pushoutFromTelescope_comp_pushoutToTelescope A a B b C c f g hf hg

end Quillen.LoopPrespectrum.Telescope
