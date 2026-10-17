/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactAttachment

/-!
# Pointwise evaluation on the unchanged common-reference nerve

A constant compact parameter supplies a set-level evaluator on every original native level.
Every simplex representative recovers the original finite family. The evaluator agrees with
all existing compact families, so its definition does not choose a simplex representative.
This file makes no assertion of joint continuity on the whole nerve times the native input.
-/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open scoped Simplicial Topology unitInterval
universe u v

namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve
variable {V W : Model.{u}} (F : V ⟶ W)

/-- Evaluate a nerve point using the existing family with constant compact parameter `Unit`. -/
def pointwisePrespectrumFamily (n : ℕ) (y : |nerve (Codiscrete (Node F))|)
    (x : (prespectrum V).space n) : (prespectrum W).space n :=
  compactPrespectrumFamily F (ContinuousMap.const Unit y) n ((), x)

/-- Every full-node simplex representative gives the same original native value. -/
theorem pointwisePrespectrumFamily_parameter {k : ℕ} (N : Fin (k + 1) → Node F)
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n (parameter F N z) x =
      prespectrumFamily F N n (z, x) :=
  compactPrespectrumFamily_eq_simplex F (ContinuousMap.const Unit (parameter F N z))
    N () z rfl n x

/-- Pointwise evaluation agrees with every original compact-parameter family. -/
theorem pointwisePrespectrumFamily_eq_compact
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |nerve (Codiscrete (Node F))|)) (n : ℕ) (t : S)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n (p t) x = compactPrespectrumFamily F p n (t, x) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F (p t)
  calc
    _ = prespectrumFamily F N n (z, x) := by
      rw [← hz]
      exact pointwisePrespectrumFamily_parameter F N n z x
    _ = _ := (compactPrespectrumFamily_eq_simplex F p N t z hz.symm n x).symm

/-- Restriction to any compact parameter has the existing joint continuity proof. -/
theorem pointwisePrespectrumFamily_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |nerve (Codiscrete (Node F))|)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      pointwisePrespectrumFamily F n (p z.1) z.2) := by
  have h : (fun z : S × (prespectrum V).space n ↦
      pointwisePrespectrumFamily F n (p z.1) z.2) = compactPrespectrumFamily F p n := by
    funext z
    exact pointwisePrespectrumFamily_eq_compact F p n z.1 z.2
  rw [h]
  exact (compactPrespectrumFamily F p n).continuous

/-- The exact original point is preserved at every level, including zero. -/
theorem pointwisePrespectrumFamily_point (n : ℕ) (y : |nerve (Codiscrete (Node F))|) :
    pointwisePrespectrumFamily F n y ((prespectrum V).point n) =
      (prespectrum W).point n :=
  compactPrespectrumFamily_point F (ContinuousMap.const Unit y) n ()

/-- The structure coordinate is independent of the fixed nerve parameter. -/
theorem pointwisePrespectrumFamily_structure (n : ℕ)
    (y : |nerve (Codiscrete (Node F))|) (x : (prespectrum V).space n) (t : I) :
    pointwisePrespectrumFamily F (n + 1) y ((prespectrum V).structureMap n x t) =
      (prespectrum W).structureMap n (pointwisePrespectrumFamily F n y x) t :=
  compactPrespectrumFamily_structure F (ContinuousMap.const Unit y) n () x t

/-- Level zero acts on the actual original input loop at its independent loop time. -/
theorem pointwisePrespectrumFamily_zero_apply (y : |nerve (Codiscrete (Node F))|)
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) (ℓ : I) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      pointwisePrespectrumFamily F 0 y γ) ℓ =
      compactStageFamily F 0 (ContinuousMap.const Unit y) ((), γ ℓ) := rfl

variable {T : Model.{u}} (J : W ⟶ T) (G : V ⟶ T)
  (ε : G.functor ≅ (F ≫ J).functor)

/-- The full-reference attachment evaluates correctly at every point of the actual nerve. -/
theorem pointwisePrespectrumFamily_attachPostcomp (n : ℕ)
    (y : |nerve (Codiscrete (Node F))|) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily G n (mapParameter (attachPostcompNode F J G ε) y) x =
      (prespectrumMap J).map n (pointwisePrespectrumFamily F n y x) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F y
  rw [← hz, mapParameter_parameter, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact prespectrumFamily_attachPostcomp F J G ε N n z x

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve
