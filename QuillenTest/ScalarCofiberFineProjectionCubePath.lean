/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberFineProjectionCubePath

/-! The actual same-rebase projection, both endpoints and its complete change-weak image. -/
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
namespace QuillenTest.ScalarCofiberFineProjectionCubePath
local instance (X : Scheme.{u}) : HasBinaryCoproducts (Perfect X) :=
  Additivity.hasBinaryCoproducts (perfectWaldhausen X)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (r : Γ(X, ⊤))
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
    (subdivisionBasepoint (perfectWaldhausen X)))
local notation "V" => perfectWaldhausen X

/-- The supplied cube is evaluated on the original horizontal endpoint and diagonal iso. -/
theorem original_input (z : Fin (n + 1) → unitInterval) :
    perfectScalarProjectionInputCube n p z =
      SSet.toTop.map (bisimplicialDiagonalIso V).hom
        (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))
          (p z)) := rfl

/-- The actual scalar additivity source is the same-rebase projection source. -/
theorem original_middle_endpoint :
    scalarFineAdditivitySourceCube X (perfectScalarInclusionNat X r)
        (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p =
      perfectOpenScalarProjectionMiddleCube j r n p :=
  perfectOpenScalarProjectionMiddleCube_eq j r n p

/-- The identity additivity source is the same-rebase projection target. -/
theorem original_identity_endpoint :
    scalarFineAdditivitySourceCube X (𝟙 (𝟭 (Perfect X))) (QuotientRows.oneIdToZero V)
        (perfectScalarIdentityFineCofibrationSequence (X := X)) n p =
      perfectOpenScalarProjectionIdentityCube j n p :=
  perfectOpenScalarProjectionIdentityCube_eq j n p

/-- The literal fine projection retains every original time and coordinate. -/
theorem original_fine_projection (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarFineProjectionCubePath j r n p t z =
      perfectOpenScalarProjectionFineRealizationHomotopy j r
        (t, separatedFirstDeloopingMap V (p z)) :=
  perfectOpenScalarFineProjectionCubePath_apply j r n p t z

/-- The full coarse projection is the actual image of the fine path. -/
theorem original_projection_image (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarFineProjectionCubePath j r n p t) z =
      perfectOpenScalarProjectionRealizationHomotopy j r
        (t, separatedFirstDeloopingMap V (p z)) :=
  perfectOpenScalarFineProjectionCubePath_changeWeak j r n p t z

/-- Every original spatial boundary point is fixed throughout the fine projection. -/
theorem original_projection_boundary (t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarFineProjectionCubePath j r n p t z = (V).kBasepoint :=
  perfectOpenScalarFineProjectionCubePath_boundary j r n p t z hz

/-- Degree zero retains the entire one-coordinate boundary at every projection time. -/
theorem original_degree_zero
    (p₀ : GenLoop (Fin (0 + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      (subdivisionBasepoint V)) (t : unitInterval) (z : Fin (0 + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (0 + 1))) :
    perfectOpenScalarFineProjectionCubePath j r 0 p₀ t z = (V).kBasepoint :=
  perfectOpenScalarFineProjectionCubePath_boundary j r 0 p₀ t z hz

end QuillenTest.ScalarCofiberFineProjectionCubePath
