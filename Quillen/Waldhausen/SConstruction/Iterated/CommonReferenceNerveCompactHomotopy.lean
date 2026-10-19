/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCubeExtension

/-!
# Original compact common-reference homotopies

Only the supplied compact parameter and its interval product are evaluated continuously.
The original concatenation and reversal clocks are retained without a whole-nerve evaluator.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve
variable {V W : Model.{u}} (F : V ⟶ W)
  {T : Type v} [TopologicalSpace T] [CompactSpace T]
  {A B C : C(T, |nerve (Codiscrete (Node F))|)}

/-- Evaluate the actual compact interval family with its independent original spectrum input. -/
def compactHomotopy (H : A.Homotopy B) (n : ℕ) :
    (compactPrespectrumFamily F A n).Homotopy (compactPrespectrumFamily F B n) where
  toFun z := compactPrespectrumFamily F H.toContinuousMap n ((z.1, z.2.1), z.2.2)
  continuous_toFun := (compactPrespectrumFamily F H.toContinuousMap n).continuous.comp
    (by fun_prop)
  map_zero_left z := compactFamily_of_point_eq F H.toContinuousMap A (0, z.1) z.1
    (H.apply_zero z.1) n z.2
  map_one_left z := compactFamily_of_point_eq F H.toContinuousMap B (1, z.1) z.1
    (H.apply_one z.1) n z.2

/-- The whole original parameter and native input are evaluated literally. -/
theorem compactHomotopy_apply (H : A.Homotopy B) (n : ℕ) (r : unitInterval)
    (t : T) (x : (prespectrum V).space n) :
    compactHomotopy F H n (r, (t, x)) =
      compactPrespectrumFamily F H.toContinuousMap n ((r, t), x) := rfl

/-- The source compact family is unchanged. -/
theorem compactHomotopy_zero (H : A.Homotopy B) (n : ℕ)
    (t : T) (x : (prespectrum V).space n) :
    compactHomotopy F H n (0, (t, x)) = compactPrespectrumFamily F A n (t, x) :=
  (compactHomotopy F H n).apply_zero (t, x)

/-- The target compact family is unchanged. -/
theorem compactHomotopy_one (H : A.Homotopy B) (n : ℕ)
    (t : T) (x : (prespectrum V).space n) :
    compactHomotopy F H n (1, (t, x)) = compactPrespectrumFamily F B n (t, x) :=
  (compactHomotopy F H n).apply_one (t, x)

/-- Reversal preserves the entire original compact homotopy, not only its endpoints. -/
theorem compactHomotopy_symm (H : A.Homotopy B) (n : ℕ) :
    compactHomotopy F H.symm n = (compactHomotopy F H n).symm := by
  apply ContinuousMap.Homotopy.ext
  rintro ⟨r, t, x⟩
  exact compactFamily_of_point_eq F H.symm.toContinuousMap H.toContinuousMap
    (r, t) (unitInterval.symm r, t) rfl n x

/-- Concatenation retains the original half clock as an equality of whole homotopies. -/
theorem compactHomotopy_trans (H : A.Homotopy B) (K : B.Homotopy C) (n : ℕ) :
    compactHomotopy F (H.trans K) n =
      (compactHomotopy F H n).trans (compactHomotopy F K n) := by
  apply ContinuousMap.Homotopy.ext
  rintro ⟨r, t, x⟩
  rw [ContinuousMap.Homotopy.trans_apply]
  split <;> rename_i hr
  · apply compactFamily_of_point_eq F _ _ _ _ ?_ n x
    change (H.trans K) (r, t) = H _
    rw [ContinuousMap.Homotopy.trans_apply, dite_eq_left hr]
  · apply compactFamily_of_point_eq F _ _ _ _ ?_ n x
    change (H.trans K) (r, t) = K _
    rw [ContinuousMap.Homotopy.trans_apply, dite_eq_right hr]

/-- Every compact homotopy fixes the original chosen point at all times. -/
theorem compactHomotopy_point (H : A.Homotopy B) (n : ℕ) (r : unitInterval) (t : T) :
    compactHomotopy F H n (r, (t, (prespectrum V).point n)) = (prespectrum W).point n :=
  compactPrespectrumFamily_point F H.toContinuousMap n (r, t)

/-- Structure time remains independent of both compact coordinates. -/
theorem compactHomotopy_structure (H : A.Homotopy B) (n : ℕ)
    (r s : unitInterval) (t : T) (x : (prespectrum V).space n) :
    compactHomotopy F H (n + 1) (r, (t, (prespectrum V).structureMap n x s)) =
      (prespectrum W).structureMap n (compactHomotopy F H n (r, (t, x))) s :=
  compactPrespectrumFamily_structure F H.toContinuousMap n (r, t) x s

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve
