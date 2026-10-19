/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.ZigzagSequentializationColimitHomotopy

/-!
# Original whole-family and strict endpoint regressions

These regressions retain independent original family, pushout-cylinder and prespectrum
structure times. Ordinary nullhomotopies have a literal zero endpoint.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open Quillen.LoopPrespectrum
open scoped unitInterval
universe u
namespace QuillenTest.ZigzagSequentializationNaturality
variable {C D : Quillen.LoopPrespectrum.{u}} {u v : C ⟶ D} (L : Homotopy u v)

/-- An arbitrary original whole family descends through the actual constant-sequence colimit. -/
def constantFamily : Homotopy
    (SequentialColimit.map (fun _ ↦ C) (fun _ ↦ 𝟙 C) (fun _ ↦ D) (fun _ ↦ 𝟙 D)
      (fun _ ↦ u) (fun _ ↦ by simp))
    (SequentialColimit.map (fun _ ↦ C) (fun _ ↦ 𝟙 C) (fun _ ↦ D) (fun _ ↦ 𝟙 D)
      (fun _ ↦ v) (fun _ ↦ by simp)) :=
  SequentialColimit.mapHomotopy _ _ _ _ _ _ _ _ (fun _ ↦ L) (fun _ _ _ _ ↦ rfl)

/-- Original family time is unchanged at an arbitrary original ordinary stage. -/
theorem constant_family_time (n k : ℕ) (r : unitInterval) (x : C.space k) :
    (constantFamily L).level k
      (r, (SequentialColimit.inclusion (fun _ ↦ C) (fun _ ↦ 𝟙 C) n).map k x) =
        (SequentialColimit.inclusion (fun _ ↦ D) (fun _ ↦ 𝟙 D) n).map k
          (L.level k (r, x)) :=
  by
    unfold constantFamily
    exact SequentialColimit.mapHomotopy_inclusion
      (fun _ ↦ C) (fun _ ↦ 𝟙 C) (fun _ ↦ D) (fun _ ↦ 𝟙 D) _ _ _ _ _ _ k n r x

/-- Family time and the original structure-loop time remain independent. -/
theorem constant_independent_structure_time (n k : ℕ) (r t : unitInterval)
    (x : C.space k) :
    (constantFamily L).level (k + 1)
        (r, (SequentialColimit.inclusion (fun _ ↦ C) (fun _ ↦ 𝟙 C) n).map (k + 1)
          (C.structureMap k x t)) =
      (SequentialColimit.inclusion (fun _ ↦ D) (fun _ ↦ 𝟙 D) n).map (k + 1)
        (D.structureMap k (L.level k (r, x)) t) := by
  rw [constant_family_time, L.comm]

variable (E V : ℕ → Quillen.LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)
    (E' V' : ℕ → Quillen.LoopPrespectrum.{u})
    (a' : ∀ n, E' n ⟶ V' n) (b' : ∀ n, E' (n + 1) ⟶ V' n)
    (d₀ d₁ : ∀ n, E n ⟶ E' n) (v₀ v₁ : ∀ n, V n ⟶ V' n)
    (ha₀ : ∀ n, a n ≫ v₀ n = d₀ n ≫ a' n)
    (hb₀ : ∀ n, b n ≫ v₀ n = d₀ (n + 1) ≫ b' n)
    (ha₁ : ∀ n, a n ≫ v₁ n = d₁ n ≫ a' n)
    (hb₁ : ∀ n, b n ≫ v₁ n = d₁ (n + 1) ≫ b' n)
    (HE : ∀ n, Homotopy (d₀ n) (d₁ n)) (HV : ∀ n, Homotopy (v₀ n) (v₁ n))
    (hA : ∀ n k r x, (HV n).level k (r, (a n).map k x) =
      (a' n).map k ((HE n).level k (r, x)))
    (hB : ∀ n k r x, (HV n).level k (r, (b n).map k x) =
      (b' n).map k ((HE (n + 1)).level k (r, x)))

/-- The original family clock and the first pushout-cylinder height are independent. -/
theorem independent_pushout_time (k : ℕ) (r s : unitInterval) (x : (E 1).space k) :
    (ZigzagSequentialization.stageHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB 2).level k
        (r, HomotopyPushout.cylinder (b 0) (a 1) k (s, x)) =
      HomotopyPushout.cylinder (b' 0) (a' 1) k (s, (HE 1).level k (r, x)) := rfl

/-- The original coherent vertex nulls give an ordinary family with a literal zero endpoint. -/
theorem literal_null_endpoint
    (NE : ∀ n, Homotopy (d₀ n) (zeroHom (E n) (E' n)))
    (NV : ∀ n, Homotopy (v₀ n) (zeroHom (V n) (V' n)))
    (hNA : ∀ n k r x, (NV n).level k (r, (a n).map k x) =
      (a' n).map k ((NE n).level k (r, x)))
    (hNB : ∀ n k r x, (NV n).level k (r, (b n).map k x) =
      (b' n).map k ((NE (n + 1)).level k (r, x)))
    (k : ℕ) (q : (ZigzagSequentialization.ordinaryColimit E V a b).space k) :
    (ZigzagSequentialization.ordinaryColimitNullhomotopy E V a b E' V' a' b'
      d₀ v₀ ha₀ hb₀ NE NV hNA hNB).level k (1, q) =
        (ZigzagSequentialization.ordinaryColimit E' V' a' b').point k :=
  (ZigzagSequentialization.ordinaryColimitNullhomotopy E V a b E' V' a' b'
    d₀ v₀ ha₀ hb₀ NE NV hNA hNB).at_one k q

end QuillenTest.ZigzagSequentializationNaturality
