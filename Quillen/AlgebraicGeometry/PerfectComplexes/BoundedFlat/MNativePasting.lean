/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MReindexedVertex

/-! Native correspondence of the literal scalar paste from actual node and finite order data. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMFamilyTransfer
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) {k : ℕ}
  (N : Fin (k + 1) → BassOverlap.Node P u v)
  (f : Fin 45 → Fin (k + 1)) (g : Fin 131 → Fin (k + 1))
  (hn : ∀ i, N (g i) = BassH1Merged.nodes P u v i)
  (hv : ∀ i, N (f i) = BassMVertex.nodes P u v i) (o : SupportOrders f g)
  (e : BassMScalarPasting.IndexEqualities f g)

include hn o in
/-- Every reassociation point retains its native value through the actual H1 target range. -/
theorem second_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (BassMReassociation.secondParameter (r, t)), x) =
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (BassMReassociation.secondParameter (r, t), x) := by
  obtain ⟨s, hs⟩ := BassMReassociation.second_in_h1_target.{u} r t
  have h := old_h1_value P u v N f g hn o n 1 s x
  rw [hs] at h
  exact h

include hn o in
/-- The full second stage remains exactly the reversed native five-piece reassociation. -/
theorem second_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (BassMReassociation.secondParameter (r, t)), x) =
    (BassMComponents.originalM P u v).level n
      (upper r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (second_value P u v N f g hn o n r t x).trans (BassMReassociation.second_native P u v n r t x)

include hn hv o in
/-- The whole paste is the literal original M, including level zero and both times. -/
theorem native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (BassMScalarPasting.parameter.{u} f g e (r, t), x) =
    (BassMComponents.originalM P u v).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  rcases cover r with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [BassMScalarPasting.parameter_lower]
    exact vertex_native P u v N f g hv o n s t x
  · rw [BassMScalarPasting.parameter_upper]
    exact second_native P u v N f g hn o n s t x

/-- The actual common family fixes the original point for every parameter in the entire M paste. -/
theorem point (n : ℕ) (r t : unitInterval) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (BassMScalarPasting.parameter.{u} f g e (r, t),
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).point n :=
  prespectrumSimplexFamily_point (nativeSimplex P u v N) n _

/-- The structure coordinate remains independent of both whole M scalar parameters. -/
theorem structure_time (n : ℕ) (r t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) (n + 1)
      (BassMScalarPasting.parameter.{u} f g e (r, t),
        (originalPrespectrum (boundedFlatPerfectWaldhausen
          (space (op P, a)))).structureMap n x z) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
        (prespectrumSimplexFamily (nativeSimplex P u v N) n
          (BassMScalarPasting.parameter.{u} f g e (r, t), x)) z :=
  prespectrumSimplexFamily_structure (nativeSimplex P u v N) n _ x z

end Quillen.PerfectComplexes.BassMFamilyTransfer
