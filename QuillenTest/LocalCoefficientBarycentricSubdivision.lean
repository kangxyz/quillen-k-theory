/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.BarycentricIterations
public import Quillen.Topology.LocalCoefficients.DegreeRaisingHomotopy
public import QuillenTest.LocalCoefficientChains

/-!
# Consumers of actual twisted barycentric subdivision

QuillenTest retain regular path-class monodromy, check the actual local differential
and chain homotopy, and consume eventual-smallness for the original coproduct
chain module. A concrete two-vertex calculation checks recursive orientations.
-/

@[expose] public section

open Quillen.LocalCoefficients


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Convexity
open scoped Simplicial

universe u v

namespace QuillenTest.LocalCoefficientBarycentricSubdivision

open Quillen

open LocalCoefficients LocalCoefficientChains

variable {X : Type u} [TopologicalSpace X]

/-- The exact recursive coning formula in dimension one has opposite face signs. -/
theorem subdivide_pair {P : Type*} (center : List P → P) (p q : P) :
    SubdivisionListChains.subdivision center (SubdivisionListChains.generator [p, q]) =
      SubdivisionListChains.generator [center [p, q], center [q]] -
        SubdivisionListChains.generator [center [p, q], center [p]] := by
  have hs (r : P) :
      SubdivisionListChains.subdivision center (SubdivisionListChains.generator [r]) =
        SubdivisionListChains.generator [center [r]] := by
    rw [SubdivisionListChains.subdivision_generator_nonempty center [r] (by simp)]
    simp
  rw [SubdivisionListChains.subdivision_generator_nonempty center [p, q] (by simp)]
  simp only [SubdivisionListChains.boundary_cons, SubdivisionListChains.boundary_nil,
    map_zero, sub_zero, SubdivisionListChains.cone_generator, map_sub, hs]

/-- Subdivision commutes with the genuine regular-system boundary in all degrees. -/
example (b : X) (V : ModuleCat.{u} ℤ) (n : ℕ) :
    (barycentricSubdivision (regularSystem b V)).f (n + 1) ≫
        (singularChainComplex (regularSystem b V)).d (n + 1) n =
      (singularChainComplex (regularSystem b V)).d (n + 1) n ≫
        (barycentricSubdivision (regularSystem b V)).f n :=
  (barycentricSubdivision (regularSystem b V)).comm _ _

/-- The actual regular-system endomorphism has the constructed chain homotopy. -/
example (b : X) (V : ModuleCat.{u} ℤ) :
    Homotopy (𝟙 (singularChainComplex (regularSystem b V)))
      (barycentricSubdivision (regularSystem b V)) :=
  barycentricSubdivisionHomotopy (regularSystem b V)

/-- Every iterate retains a chain homotopy to the same original identity. -/
example (b : X) (V : ModuleCat.{u} ℤ) (k : ℕ) :
    Homotopy (𝟙 (singularChainComplex (regularSystem b V)))
      (barycentricSubdivisionIterate (regularSystem b V) k) :=
  barycentricSubdivisionIterateHomotopy (regularSystem b V) k

/-- Coefficients on a reparametrized simplex really concatenate the original
path class with the path inside its source simplex. -/
theorem regular_affine_term_generator (b : X) (V : ModuleCat.{u} ℤ) {N n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1)))
    (f : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (N + 1))))
    (q : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk (σ x)) :
    Sigma.ι (fun _ : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk (σ x) ↦ V) q ≫
        transportedSimplexTerm (regularSystem b V) σ x f =
      Sigma.ι (fun _ : FundamentalGroupoid.mk b ⟶
          FundamentalGroupoid.mk (σ (f (StdSimplex.single 0))) ↦ V)
        (q ≫ Path.Homotopic.Quotient.mk
          ((PathConnectedSpace.somePath x (f (StdSimplex.single 0))).map σ.continuous)) ≫
        chainInclusion (regularSystem b V) (σ.comp f) := by
  unfold transportedSimplexTerm simplexTransport
  rw [← Category.assoc, regular_transport_generator]

/-- Every regular-system coefficient on a fixed simplex is eventually small,
with one bound valid at every larger subdivision depth. -/
example {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (b : X) (V : ModuleCat.{u} ℤ)
    {n : ℕ} (σ : SingularSimplex X ⦋n⦌) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m → ∀ a : simplexFiber (regularSystem b V) σ,
      (chainInclusion (regularSystem b V) σ ≫
        (barycentricSubdivisionIterate (regularSystem b V) m).f n) a ∈
          smallChainSubmodule U (regularSystem b V) n :=
  exists_barycentricSubdivisionIterate_simplex_mem U hU hcover (regularSystem b V) σ

end QuillenTest.LocalCoefficientBarycentricSubdivision
