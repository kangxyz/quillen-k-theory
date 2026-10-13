/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.Prespectrum.TelescopeCompactness
import Quillen.Waldhausen.SConstruction.Iterated.Separation

/-!
# Original-map consumers of reduced telescope compactness

These consumers use the unchanged based cubical sphere representatives and
boundary-relative homotopies in the original telescope. The iterated-S consumer
has no assumed T1 instance: it uses the separation theorem for the actual
realizations and degree-zero loop space.
-/

open CategoryTheory Set
open scoped unitInterval
open Quillen Quillen.LoopPrespectrum

namespace QuillenTest.TelescopeCompactness

open Quillen

universe u
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (k : ℕ) [∀ i, T1Space ((E i).space k)]

/-- Original sphere representatives have bounded cylinder support and unchanged boundary. -/
theorem based_sphere_support (n : ℕ)
    (p : GenLoop (Fin n) (Telescope.Space E f k) (Telescope.point E f k)) :
    ∃ N : ℕ,
      (∀ z, ∃ i ≤ N, ∃ w, Telescope.cylinder E f k i w = p z) ∧
      (∀ z ∈ Cube.boundary (Fin n), p z = Telescope.point E f k) := by
  obtain ⟨N, hN⟩ := Telescope.exists_cylinder_bound E f k p.val
  exact ⟨N, hN, p.property⟩

/-- A based homotopy has one bound simultaneously valid for both original endpoint maps. -/
theorem based_homotopy_common_support (n : ℕ)
    {p q : GenLoop (Fin n) (Telescope.Space E f k) (Telescope.point E f k)}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) :
    ∃ N : ℕ,
      (∀ t z, ∃ i ≤ N, ∃ w, Telescope.cylinder E f k i w = H (t, z)) ∧
      (∀ z, ∃ i ≤ N, ∃ w, Telescope.cylinder E f k i w = p z) ∧
      (∀ z, ∃ i ≤ N, ∃ w, Telescope.cylinder E f k i w = q z) := by
  obtain ⟨N, hN⟩ := Telescope.exists_homotopy_cylinder_bound E f k H.toHomotopy.toContinuousMap
  refine ⟨N, hN, fun z ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨i, hi, w, hw⟩ := hN 0 z
    exact ⟨i, hi, w, hw.trans (H.apply_zero z)⟩
  · obtain ⟨i, hi, w, hw⟩ := hN 1 z
    exact ⟨i, hi, w, hw.trans (H.apply_one z)⟩

/-- Every original homotopy-group class admits a representative with bounded support. -/
theorem homotopy_class_support (n : ℕ)
    (a : HomotopyGroup.Pi n (Telescope.Space E f k) (Telescope.point E f k)) :
    ∃ p : GenLoop (Fin n) (Telescope.Space E f k) (Telescope.point E f k),
      Quotient.mk' p = a ∧
      ∃ N : ℕ, ∀ z, ∃ i ≤ N, ∃ w, Telescope.cylinder E f k i w = p z := by
  induction a using Quotient.inductionOn with
  | h p => exact ⟨p, rfl, Telescope.exists_cylinder_bound E f k p.val⟩

/-- T1 separation is proved for the original iterated-S spaces, rather than assumed. -/
theorem iteratedS_sphere_support (W : ℕ → Waldhausen.IteratedS.Model.{u})
    (F : ∀ i, W i ⟶ W (i + 1)) (k n : ℕ)
    (p : GenLoop (Fin n)
      (Telescope.Space (fun i ↦ Waldhausen.IteratedS.prespectrum (W i))
        (fun i ↦ Waldhausen.IteratedS.prespectrumMap (F i)) k)
      (Telescope.point (fun i ↦ Waldhausen.IteratedS.prespectrum (W i))
        (fun i ↦ Waldhausen.IteratedS.prespectrumMap (F i)) k)) :
    ∃ N : ℕ, ∀ z, ∃ i ≤ N, ∃ w,
      Telescope.cylinder (fun i ↦ Waldhausen.IteratedS.prespectrum (W i))
        (fun i ↦ Waldhausen.IteratedS.prespectrumMap (F i)) k i w = p z :=
  Telescope.exists_cylinder_bound _ _ _ p.val

omit [∀ i, T1Space ((E i).space k)] in
/-- Upper endpoints sent to the stage basepoint really belong to the collapsed fiber. -/
theorem upper_endpoint_collapsed (i : ℕ) (x : (E i).space k)
    (hx : (f i).map k x = (E (i + 1)).point k) :
    Telescope.cylinder E f k i (1, x) = Telescope.point E f k := by
  rw [Telescope.cylinder_one, hx, Telescope.cylinder_point]

end QuillenTest.TelescopeCompactness
