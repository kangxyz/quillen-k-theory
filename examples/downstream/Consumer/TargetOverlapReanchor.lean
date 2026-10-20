/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetOverlapReanchor

/-! # Two literal reference changes on an arbitrary finite-dimensional old overlap family -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open scoped Simplicial Topology unitInterval

universe u

namespace Consumer.TargetOverlapReanchor

open CommonReferenceNerve CommonReferenceProduct

/-- Successive whole-reference placements retain all external, comparison and overlap times. -/
theorem successive_cube_references {R : CommRingCat.{u}} (P : Over (Spec R))
    {a b : Under R} (f : a ⟶ b) {V : Model.{u + 1}}
    (E E' E'' : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (δ : E'.functor ≅ E.functor) (ε : E''.functor ≅ E'.functor)
    (d : ℕ) (p : C(Fin d → I, |nerve (Codiscrete (CommonReferenceNerve.Node E))|))
    (z : Fin d → I) (s t : I) :
    mapParameter (reanchor (F₀ := reference P f E'') (F₁ := reference P f E')
      (isoWhiskerRight ε (BassH0Diagram.reference P f).functor))
      (mapParameter (reanchor (F₀ := reference P f E') (F₁ := reference P f E)
        (isoWhiskerRight δ (BassH0Diagram.reference P f).functor))
        (overlap P f E (p z, (s, t)))) =
    overlap P f E''
      (mapParameter (reanchor (F₀ := E'') (F₁ := E') ε)
        (mapParameter (reanchor (F₀ := E') (F₁ := E) δ) (p z)), (s, t)) := by
  rw [overlap_reanchor P f E E' δ, overlap_reanchor P f E' E'' ε]

end Consumer.TargetOverlapReanchor
