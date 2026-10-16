/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberCubeSquare

/-! # Original cube coordinates, four whole edges and the constructive boundary homotopy -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u
namespace QuillenTest.ScalarCofiberCubeSquare
local instance (X : Scheme.{u}) : HasBinaryCoproducts (Perfect X) :=
  Additivity.hasBinaryCoproducts (perfectWaldhausen X)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
    (subdivisionBasepoint (perfectWaldhausen X)))
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)

/-- The exact original producer remains visible in a strict public client. -/
theorem original_coordinates (t s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (t, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (perfectOpenScalarBasedAdditivitySquare j r q hq (t, (s, p z))) :=
  perfectOpenScalarCofiberCubeSquare_apply j r q hq n p t s z

/-- The exact original producer remains visible in a strict public client. -/
theorem original_full_square_boundary (t s : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarCofiberCubeSquare j r q hq n p (t, s) z = (W).kBasepoint :=
  perfectOpenScalarCofiberCubeSquare_boundary j r q hq n p t s z hz

/-- The exact original producer remains visible in a strict public client. -/
theorem original_boundary_interpolation :
    perfectOpenScalarCofiberCubeBoundaryHomotopy j r q hq n p =
      (squareBoundaryPathHomotopy
        (perfectOpenScalarCofiberCubeSquare j r q hq n p)).symm :=
  perfectOpenScalarCofiberCubeBoundaryHomotopy_eq j r q hq n p

/-- The exact original producer remains visible in a strict public client. -/
theorem original_full_homotopy_boundary (a t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarCofiberCubeBoundaryHomotopy j r q hq n p (a, t) z = (W).kBasepoint :=
  perfectOpenScalarCofiberCubeBoundaryHomotopy_boundary j r q hq n p a t z hz

/-- The literal edge keeps its whole original face at every time and cube point. -/
theorem original_identity_edge (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeIdentityPath j r q hq n p s z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (subdividedBasedAdditivityHomotopy (perfectWaldhausen X) W
          (𝟙 (𝟭 (Perfect X))) (QuotientRows.oneIdToZero W)
          (perfectOpenScalarIdentityCofibrationSequence j) (s, p z)) :=
  (perfectOpenScalarCofiberCubeIdentityPath_apply j r q hq n p s z).trans
    (perfectOpenScalarCofiberCubeSquare_transformation_zero j r q hq n p s z)

/-- The literal edge keeps its whole original face at every time and cube point. -/
theorem original_scalar_edge (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeScalarPath j r q hq n p s z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (subdividedBasedAdditivityHomotopy (perfectWaldhausen X) W
          (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
          (perfectOpenScalarCofibrationSequence j r) (s, p z)) :=
  (perfectOpenScalarCofiberCubeScalarPath_apply j r q hq n p s z).trans
    (perfectOpenScalarCofiberCubeSquare_transformation_one j r q hq n p s z)

/-- The literal edge keeps its whole original face at every time and cube point. -/
theorem original_inclusion_edge (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeInclusionPath j r q hq n p t z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarInclusionDiagonalHomotopy j r q hq)
          (t, realizedDiagonalMap
            (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet (perfectWaldhausen X)))
            (p z))) :=
  (perfectOpenScalarCofiberCubeInclusionPath_apply j r q hq n p t z).trans
    (perfectOpenScalarCofiberCubeSquare_additivity_zero j r q hq n p t z)

/-- The literal edge keeps its whole original face at every time and cube point. -/
theorem original_sum_edge (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCofiberCubeSumPath j r q hq n p t z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarSumDiagonalHomotopy j r q hq)
          (t, p z)) :=
  (perfectOpenScalarCofiberCubeSumPath_apply j r q hq n p t z).trans
    (perfectOpenScalarCofiberCubeSquare_additivity_one j r q hq n p t z)

/-- Degree zero still uses the actual one-coordinate cube and the complete spatial boundary. -/
theorem original_degree_zero
    (p₀ : GenLoop (Fin (0 + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
      (subdivisionBasepoint (perfectWaldhausen X)))
    (a t : unitInterval) (z : Fin (0 + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (0 + 1))) :
    perfectOpenScalarCofiberCubeBoundaryHomotopy j r q hq 0 p₀ (a, t) z = (W).kBasepoint :=
  perfectOpenScalarCofiberCubeBoundaryHomotopy_boundary j r q hq 0 p₀ a t z hz

end QuillenTest.ScalarCofiberCubeSquare
