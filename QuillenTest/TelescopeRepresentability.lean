/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.Prespectrum.TelescopeEventualHomotopy
import Quillen.Waldhausen.SConstruction.Iterated.Separation

/-!
# Original-stage consumers of telescope representability

Actual iterated-S telescopes admit original-stage representatives. Equality and
nullhomotopy in the actual quotient are detected by original finite transitions.
The cylinder sweep regression keeps the original stage and independent structure
parameter, without supplying a replacement homotopy-group model.
-/

open CategoryTheory Set
open scoped unitInterval
open Quillen Quillen.LoopPrespectrum

namespace QuillenTest.TelescopeRepresentability

open Quillen

universe u
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (k : ℕ) [∀ i, T1Space ((E i).space k)]

/-- A telescope-null original sphere becomes null after an actual finite composite. -/
theorem eventual_original_nullhomotopy (n i : ℕ)
    (p : GenLoop (Fin n) ((E i).space k) ((E i).point k))
    (h : GenLoop.Homotopic
      (genLoopPostcomp ((Telescope.inclusion E f i).map k)
        ((Telescope.inclusion E f i).map_point k) p) GenLoop.const) :
    ∃ N : ℕ, ∃ hi : i ≤ N, GenLoop.Homotopic
      (genLoopPostcomp ((Telescope.transition E f i N hi).map k)
        ((Telescope.transition E f i N hi).map_point k) p) GenLoop.const := by
  have h' : GenLoop.Homotopic
      (genLoopPostcomp ((Telescope.inclusion E f i).map k)
        ((Telescope.inclusion E f i).map_point k) p)
      (genLoopPostcomp ((Telescope.inclusion E f i).map k)
        ((Telescope.inclusion E f i).map_point k) GenLoop.const) := by
    simpa only [genLoopPostcomp_const] using h
  obtain ⟨N, hi, hj, hN⟩ := Telescope.exists_eventual_genLoop_homotopy E f k n p GenLoop.const h'
  exact ⟨N, hi, by simpa only [genLoopPostcomp_const] using hN⟩

/-- Every class of an actual iterated-S telescope is the image of an original S-stage class. -/
theorem iteratedS_original_stage_surjectivity (W : ℕ → Waldhausen.IteratedS.Model.{u})
    (F : ∀ i, W i ⟶ W (i + 1)) (k n : ℕ)
    (a : HomotopyGroup.Pi n
      (Telescope.Space (fun i ↦ Waldhausen.IteratedS.prespectrum (W i))
        (fun i ↦ Waldhausen.IteratedS.prespectrumMap (F i)) k)
      (Telescope.point (fun i ↦ Waldhausen.IteratedS.prespectrum (W i))
        (fun i ↦ Waldhausen.IteratedS.prespectrumMap (F i)) k)) :
    ∃ N : ℕ, ∃ b : HomotopyGroup.Pi n
      ((Waldhausen.IteratedS.prespectrum (W N)).space k)
      ((Waldhausen.IteratedS.prespectrum (W N)).point k),
      homotopyGroupMap
        ((Telescope.inclusion (fun i ↦ Waldhausen.IteratedS.prespectrum (W i))
          (fun i ↦ Waldhausen.IteratedS.prespectrumMap (F i)) N).map k)
        ((Telescope.inclusion (fun i ↦ Waldhausen.IteratedS.prespectrum (W i))
          (fun i ↦ Waldhausen.IteratedS.prespectrumMap (F i)) N).map_point k) b = a :=
  Telescope.exists_homotopyGroup_representative _ _ _ _ a

omit [∀ i, T1Space ((E i).space k)] in
/-- The original sweep raises only cylinder time and retains the independent structure time. -/
theorem sweep_original_structure (N i : ℕ) (hi : i < N)
    (x : (E i).space k) (r s t : unitInterval) :
    Telescope.sweepFamily E f N (k + 1)
      (Telescope.cylinder E f (k + 1) i (r, (E i).structureMap k x t)) s =
      Telescope.cylinder E f (k + 1) N
        (s, (E N).structureMap k ((Telescope.transition E f i N hi.le).map k x) t) := by
  rw [Telescope.sweepFamily_cylinder, Telescope.sweepPiece_of_lt E f hi]
  exact congrArg (fun y ↦ Telescope.cylinder E f (k + 1) N (s, y))
    (congrArg (fun p ↦ p t) ((Telescope.transition E f i N hi.le).comm k x))

end QuillenTest.TelescopeRepresentability
