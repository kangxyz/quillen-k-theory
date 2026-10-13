/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.TelescopeHomotopy
public import Quillen.Topology.Prespectrum.HomotopyPushout
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# Original pushouts into the telescope of pushouts

The actual three-corner tower induces the same reduced pushout tower. Telescoping the two
original inclusions and the whole overlap cylinders gives a map from the original pushout
of telescopes. All cylinder coordinates remain literal and independent.
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

/-- Every transition acts on the three original corners and the full pushout cylinder. -/
def pushoutTransition (i : ℕ) : HomotopyPushout.prespectrum (f i) (g i) ⟶
    HomotopyPushout.prespectrum (f (i + 1)) (g (i + 1)) :=
  HomotopyPushout.map (f i) (g i) (f (i + 1)) (g (i + 1))
    (a i) (b i) (c i) (hf i) (hg i)

/-- The original left inclusions induce the unchanged map of their telescopes. -/
def pushoutInl : prespectrum B b ⟶
    prespectrum (fun i => HomotopyPushout.prespectrum (f i) (g i))
      (pushoutTransition A a B b C c f g hf hg) :=
  map B b (fun i => HomotopyPushout.prespectrum (f i) (g i))
    (pushoutTransition A a B b C c f g hf hg) (fun i => HomotopyPushout.inl (f i) (g i))
    (fun _i => HomotopyPushout.inl_map ..)

/-- The original right inclusions induce the unchanged map of their telescopes. -/
def pushoutInr : prespectrum C c ⟶
    prespectrum (fun i => HomotopyPushout.prespectrum (f i) (g i))
      (pushoutTransition A a B b C c f g hf hg) :=
  map C c (fun i => HomotopyPushout.prespectrum (f i) (g i))
    (pushoutTransition A a B b C c f g hf hg) (fun i => HomotopyPushout.inr (f i) (g i))
    (fun _i => HomotopyPushout.inr_map ..)

/-- All original overlap tracks descend with independent telescope height and pushout time. -/
def pushoutGlue :
    Homotopy (map A a B b f hf ≫ pushoutInl A a B b C c f g hf hg)
      (map A a C c g hg ≫ pushoutInr A a B b C c f g hf hg) := by
  let H := mapHomotopy A a (fun i => HomotopyPushout.prespectrum (f i) (g i))
    (pushoutTransition A a B b C c f g hf hg)
    (fun i => f i ≫ HomotopyPushout.inl (f i) (g i))
    (fun i => g i ≫ HomotopyPushout.inr (f i) (g i))
    (by
      intro i
      apply Hom.ext
      funext k
      ext x
      exact congrArg (HomotopyPushout.left (f (i + 1)) (g (i + 1)) k)
        (congrArg (fun m => m.map k x) (hf i)))
    (by
      intro i
      apply Hom.ext
      funext k
      ext x
      exact congrArg (HomotopyPushout.right (f (i + 1)) (g (i + 1)) k)
        (congrArg (fun m => m.map k x) (hg i)))
    (fun i => HomotopyPushout.glue (f i) (g i)) (by intros; rfl)
  exact H.cast (by apply hom_ext; intros; rfl) (by apply hom_ext; intros; rfl)

/-- Descend the original two telescope legs with their genuine full overlap homotopy. -/
def pushoutToTelescope : HomotopyPushout.prespectrum (map A a B b f hf) (map A a C c g hg) ⟶
    prespectrum (fun i => HomotopyPushout.prespectrum (f i) (g i))
      (pushoutTransition A a B b C c f g hf hg) :=
  HomotopyPushout.desc (map A a B b f hf) (map A a C c g hg)
    (pushoutInl A a B b C c f g hf hg) (pushoutInr A a B b C c f g hf hg)
    (pushoutGlue A a B b C c f g hf hg)

/-- Left generators retain their original telescope heights. -/
theorem pushoutToTelescope_left (k i : ℕ) (t : unitInterval) (x : (B i).space k) :
    (pushoutToTelescope A a B b C c f g hf hg).map k
      (HomotopyPushout.left (map A a B b f hf) (map A a C c g hg) k
        (cylinder B b k i (t, x))) =
      cylinder (fun i => HomotopyPushout.prespectrum (f i) (g i))
        (pushoutTransition A a B b C c f g hf hg) k i
        (t, HomotopyPushout.left (f i) (g i) k x) := rfl

/-- Right generators retain their original telescope heights. -/
theorem pushoutToTelescope_right (k i : ℕ) (t : unitInterval) (x : (C i).space k) :
    (pushoutToTelescope A a B b C c f g hf hg).map k
      (HomotopyPushout.right (map A a B b f hf) (map A a C c g hg) k
        (cylinder C c k i (t, x))) =
      cylinder (fun i => HomotopyPushout.prespectrum (f i) (g i))
        (pushoutTransition A a B b C c f g hf hg) k i
        (t, HomotopyPushout.right (f i) (g i) k x) := rfl

/-- Pushout time and telescope height remain the same independent original parameters. -/
theorem pushoutToTelescope_cylinder (k i : ℕ) (s t : unitInterval) (x : (A i).space k) :
    (pushoutToTelescope A a B b C c f g hf hg).map k
      (HomotopyPushout.cylinder (map A a B b f hf) (map A a C c g hg) k
        (s, cylinder A a k i (t, x))) =
      cylinder (fun i => HomotopyPushout.prespectrum (f i) (g i))
        (pushoutTransition A a B b C c f g hf hg) k i
        (t, HomotopyPushout.cylinder (f i) (g i) k (s, x)) := rfl

end Quillen.LoopPrespectrum.Telescope
