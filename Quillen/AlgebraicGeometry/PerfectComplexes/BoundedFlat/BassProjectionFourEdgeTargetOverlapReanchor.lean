/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteParameterNaturality
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeReanchorReferences
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetOverlap

/-!
# Reanchoring the whole original target overlap

The original 31-node H0 surface and all four old overlap cells commute strictly with a
change of their complete input reference. The comparison and overlap coordinates stay
independent, also for arbitrary external parameter families. No native filler or
naturality of a newly chosen extension is assumed. The two polynomial sectors and the
whole target cone action are not asserted by this leaf.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v

namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target

open CommonReferenceNerve CommonReferenceProduct

-- Keep the finite-parameter square abstract until its full-node equality is supplied.
private theorem parameter_reanchor {A B C : Model.{u}} {E₀ E₁ : A ⟶ B}
    (G : B ⟶ C) (η : E₁.functor ≅ E₀.functor) {q : ℕ}
    (g₀ : CommonReferenceNerve.Node E₀ → Fin (q + 1) →
      CommonReferenceNerve.Node (E₀ ≫ G))
    (g₁ : CommonReferenceNerve.Node E₁ → Fin (q + 1) →
      CommonReferenceNerve.Node (E₁ ≫ G))
    (h : ∀ e j, g₁ (reanchor η e) j =
      reanchor (isoWhiskerRight η G.functor) (g₀ e j))
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E₀))|)
    (w : Convexity.StdSimplex ℝ (Fin (q + 1))) :
    mapParameter (reanchor (isoWhiskerRight η G.functor))
        (FiniteParameter.parameter E₀ (E₀ ≫ G) g₀ (y, w)) =
      FiniteParameter.parameter E₁ (E₁ ≫ G) g₁ (mapParameter (reanchor η) y, w) := by
  exact FiniteParameter.parameter_naturality
    (E := E₀) (E' := E₁) (F := E₀ ≫ G) (F' := E₁ ≫ G) (q := q)
    (reanchor η) (reanchor (isoWhiskerRight η G.functor)) g₀ g₁
    (fun e j ↦ (h e j).symm) y w

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  {V : Model.{u + 1}}
  (E E' : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (δ : E'.functor ≅ E.functor)

/-- Every original H0 node retains both its underlying model map and its full anchor. -/
theorem nodes_reanchor (N : CommonReferenceNerve.Node E) (j : Fin 31) :
    nodes P f E' (reanchor δ N) j =
      reanchor (isoWhiskerRight δ (BassH0Diagram.reference P f).functor)
        (nodes P f E N j) :=
  Reanchor.pair_whiskering (BassH0Diagram.reference P f) δ N (BassH0Diagram.nodes P f j)

/-- The entire old surface commutes before native evaluation, with both clocks unchanged. -/
theorem overlap_reanchor (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (s t : I) :
    mapParameter (reanchor (isoWhiskerRight δ (BassH0Diagram.reference P f).functor))
      (overlap P f E (y, (s, t))) =
    overlap P f E' (mapParameter (reanchor δ) y, (s, t)) := by
  change mapParameter
      (reanchor (isoWhiskerRight δ (BassH0Diagram.reference P f).functor))
      (FiniteParameter.parameter E (reference P f E) (nodes P f E)
        (y, BassH0Diagram.parameter (s, t))) =
    FiniteParameter.parameter E' (reference P f E') (nodes P f E')
      (mapParameter (reanchor δ) y, BassH0Diagram.parameter (s, t))
  exact parameter_reanchor (q := 30) (BassH0Diagram.reference P f) δ
    (nodes P f E) (nodes P f E') (nodes_reanchor P f E E' δ)
    y (BassH0Diagram.parameter (s, t))

/-- Restricting the old overlap clock retains every full reanchored cell value. -/
theorem cell_reanchor (clock : C(I, I))
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s t : I) :
    mapParameter (reanchor (isoWhiskerRight δ (BassH0Diagram.reference P f).functor))
      (cell P f E clock (y, (s, t))) =
    cell P f E' clock (mapParameter (reanchor δ) y, (s, t)) :=
  overlap_reanchor P f E E' δ y s (clock t)

/-- Arbitrary external parameters retain the two original times as separate product factors. -/
theorem overlap_reanchor_family {S : Type v} [TopologicalSpace S]
    (p : C(S, |nerve (Codiscrete (CommonReferenceNerve.Node E))|)) :
    (mapParameter (reanchor (isoWhiskerRight δ (BassH0Diagram.reference P f).functor))).comp
        ((overlap P f E).comp (p.prodMap (ContinuousMap.id (I × I)))) =
      (overlap P f E').comp
        (((mapParameter (reanchor δ)).comp p).prodMap (ContinuousMap.id (I × I))) := by
  ext ⟨z, s, t⟩
  exact overlap_reanchor P f E E' δ (p z) s t

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
