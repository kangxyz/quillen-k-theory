/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberSumCubeNormalization

/-! # Original normalization square, fine Theta paths and whole boundary clients -/
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
namespace QuillenTest.ScalarCofiberSumCubeNormalization
local instance scalarSumCubeTestCoproducts (X : Scheme.{u}) : HasBinaryCoproducts (Perfect X) :=
  Additivity.hasBinaryCoproducts (perfectWaldhausen X)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
    (subdivisionBasepoint (perfectWaldhausen X)))
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)

/-- Both independent square times and every original input coordinate remain literal. -/
theorem original_square (t s : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (s, p z))) :=
  perfectOpenScalarSumNormalizationCubeSquare_apply j r q hq n p t s z

/-- The complete old quotient-first sum edge is retained. -/
theorem original_sum_edge (s : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (0, s) z =
      perfectOpenScalarCofiberCubeSumPath j r q hq n p s z :=
  perfectOpenScalarSumNormalizationCubeSquare_vertical_zero j r q hq n p s z

/-- The complete canonical cylinder is retained before its later reversal. -/
theorem original_canonical_edge (s : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (1, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (s, p z)) :=
  perfectOpenScalarSumNormalizationCubeSquare_vertical_one j r q hq n p s z

/-- The full zero Theta face keeps its original time. -/
theorem original_zero_theta_edge (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, 0) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j)
          (t, p z)) :=
  perfectOpenScalarSumNormalizationCubeSquare_horizontal_zero j r q hq n p t z

/-- The full cone Theta face keeps its original time. -/
theorem original_cone_theta_edge (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq n p (t, 1) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q
          hq) (t, p z)) :=
  perfectOpenScalarSumNormalizationCubeSquare_horizontal_one j r q hq n p t z

/-- The fine zero normalization path is mapped without altering either time or input. -/
theorem original_fine_zero_image (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarZeroThetaFineCubePath j n p t) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j)
          (t, p z)) :=
  perfectOpenScalarZeroThetaFineCubePath_changeWeak j n p t z

/-- The fine cone normalization path has the same whole coarse cylinder. -/
theorem original_fine_cone_image (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCubeChangeWeak j n
        (perfectOpenScalarConeThetaFineCubePath j r q hq n p t) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q
          hq) (t, p z)) :=
  perfectOpenScalarConeThetaFineCubePath_changeWeak j r q hq n p t z

/-- The actual unreversed square gives exactly Z then Theta1 versus Theta0 then canonical. -/
def originalBoundaryWord :
    ((perfectOpenScalarSumNormalizationOriginalPath j r q hq n p).trans
      (perfectOpenScalarSumNormalizationConeThetaPath j r q hq n p)).Homotopy
      ((perfectOpenScalarSumNormalizationZeroThetaPath j r q hq n p).trans
        (perfectOpenScalarSumNormalizationCanonicalPath j r q hq n p)) :=
  perfectOpenScalarSumNormalizationCubeBoundaryHomotopy j r q hq n p

/-- Every spatial boundary remains fixed at two independent interpolation times. -/
theorem original_entire_boundary (a t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarSumNormalizationCubeBoundaryHomotopy j r q hq n p (a, t) z =
      (W).kBasepoint :=
  perfectOpenScalarSumNormalizationCubeBoundaryHomotopy_boundary j r q hq n p a t z hz

/-- The same full square retains a single original spatial coordinate in degree zero. -/
theorem original_degree_zero (p0 : GenLoop (Fin 1)
    |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
    (subdivisionBasepoint (perfectWaldhausen X))) (t s : unitInterval)
    (z : Fin 1 → unitInterval) :
    perfectOpenScalarSumNormalizationCubeSquare j r q hq 0 p0 (t, s) z =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (s, p0 z))) :=
  perfectOpenScalarSumNormalizationCubeSquare_apply j r q hq 0 p0 t s z

local notation "V" => perfectWaldhausen X
local notation "NW" => perfectOpenNested j
local notation "F" => perfectOpenScalarCubeChangeWeak j n
local notation "af" => scalarFineAdditivitySourceCube X (𝟙 (𝟭 (Perfect X)))
  (QuotientRows.oneIdToZero V) (perfectScalarIdentityFineCofibrationSequence (X := X)) n p
local notation "df" => scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
  (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p

/-- The original zero normalization target is transported by the actual compact comparison. -/
theorem original_zero_target_cast :
    perfectOpenScalarZeroThetaCompactPath j n p =
      (perfectOpenScalarZeroThetaFineCubePath j n p).cast rfl
        (perfectOpenScalarZeroThetaFineCubeFamily_compact j n p).symm := rfl

/-- The original cone normalization target retains the quotient-first compact comparison. -/
theorem original_cone_target_cast :
    perfectOpenScalarConeThetaCompactPath j r q hq n p =
      (perfectOpenScalarConeThetaFineCubePath j r q hq n p).cast rfl
        (perfectOpenScalarConeThetaFineCubeFamily_compact j r q hq n p).symm := rfl

/-- The full zero Theta cylinder is unchanged by the actual target cast. -/
theorem original_compact_zero_time (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarZeroThetaCompactPath j n p t z =
      SSet.toTop.map (bisimplicialDiagonalIso V).hom
        (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)
          (t, p z)) :=
  perfectOpenScalarZeroThetaCompactPath_apply j n p t z

/-- The full cone Theta cylinder retains its own original time and original spatial input. -/
theorem original_compact_cone_time (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarConeThetaCompactPath j r q hq n p t z =
      SSet.toTop.map (bisimplicialDiagonalIso V).hom
        (realizationSimplicialHomotopy (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)
          (t, p z)) :=
  perfectOpenScalarConeThetaCompactPath_apply j r q hq n p t z

/-- The geometric Theta word is constructed from the original data, with no supplied comparison. -/
def originalGeometricTheta :
    (perfectOpenScalarFineCubeSumPath j r q hq n p).symm.Homotopy
      ((CompactCoproductEndpoint.thetaOne V NW n
        (perfectOpenScalarConeThetaCompactPath j r q hq n p)).trans
        ((coproductCubePath W n (perfectOpenScalarCanonicalNullPath j r q hq n p)
          (Path.refl (F (perfectOpenScalarCanonicalRightCube j n p)))).trans
            (CompactCoproductEndpoint.thetaZero V NW n
              (perfectOpenScalarZeroThetaCompactPath j n p)).symm)) :=
  perfectOpenScalarSumNormalizationThetaHomotopy j r q hq n p

/-- Every independent Theta comparison time keeps the whole spatial boundary. -/
theorem original_geometric_theta_boundary (s t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarSumNormalizationThetaHomotopy j r q hq n p (s, t) z = (W).kBasepoint :=
  perfectOpenScalarSumNormalizationThetaHomotopy_boundary j r q hq n p s t z hz

/-- The original identity-sequence path and distinct right coordinate both survive in gamma. -/
theorem original_identity_gamma :
    perfectOpenScalarNormalizationGamma j n p =
      (perfectOpenScalarIdentityFineCubePath n p).trans
        ((perfectOpenScalarZeroThetaCompactPath j n p).trans
          (coproductLeftUnitPath V n (perfectOpenScalarCanonicalRightCube j n p))) := rfl

/-- The fine return retains the actual inverse-prefix cancellation after the entire gamma. -/
theorem original_fine_cancellation :
    perfectOpenScalarNormalizationNu j n p =
      ((perfectOpenScalarNormalizationGamma j n p).symm.map
        (GenLoopPrefix.inversePrefix n af).continuous).trans
          (GenLoopPrefix.cancellation n af) := rfl

/-- The fine endpoint uses q-first spatial separation and the complete actual return tail. -/
theorem original_fine_delta :
    perfectOpenScalarNormalizedFineDelta j r q hq n p =
      (((perfectOpenScalarConeThetaCompactPath j r q hq n p).trans
        (coproductSeparationPath n V (perfectOpenScalarCanonicalConeCube j r q hq n p)
          (perfectOpenScalarCanonicalRightCube j n p))).map
            (GenLoopPrefix.inversePrefix n af).continuous).trans
              (GenLoopPrefix.tail n (GenLoop.symmAt 0 af)
                (perfectOpenScalarCanonicalRightCube j n p)
                (perfectOpenScalarCanonicalConeCube j r q hq n p)
                (perfectOpenScalarNormalizationNu j n p)) := rfl

/-- The original coarse cancellation and hprefix source cast remain explicit. -/
theorem original_coarse_cancellation_cast :
    perfectOpenScalarNormalizedTerminalNull j r q hq n p =
      ((((perfectOpenScalarFineCubeSumPath j r q hq n p).symm.trans
        ((perfectOpenScalarIdentityFineCubePath n p).map (F).continuous).symm).map
          (GenLoopPrefix.inversePrefix n (F af)).continuous).trans
            (GenLoopPrefix.cancellation n (F af))).cast
              (CompactCoproductEndpoint.prefix_source V NW n af df) rfl := rfl

/-- Whole fine-delta naturality retains the inverse hprefix source transport. -/
theorem original_delta_naturality :
    ((perfectOpenScalarNormalizedFineDelta j r q hq n p).map (F).continuous).cast
        (CompactCoproductEndpoint.prefix_source V NW n af df).symm rfl =
      CompactCoproductEndpoint.coarseDelta V NW n
        (perfectOpenScalarIdentityFineCubePath n p) (perfectOpenScalarZeroThetaCompactPath j n p)
        (perfectOpenScalarConeThetaCompactPath j r q hq n p) :=
  CompactCoproductEndpoint.delta_map V NW n
    (perfectOpenScalarIdentityFineCubePath n p) (perfectOpenScalarZeroThetaCompactPath j n p)
    (perfectOpenScalarConeThetaCompactPath j r q hq n p)

/-- The full endpoint comparison needs only the original scalar/unit data and original cube. -/
def originalConstructedEndpoint :
    (perfectOpenScalarNormalizedTerminalNull j r q hq n p).Homotopy
      (((perfectOpenScalarNormalizedFineDelta j r q hq n p).map (F).continuous).trans
        (perfectOpenScalarCanonicalNullPath j r q hq n p)) :=
  perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p

/-- The initial whole path retains the original moving-endpoint terminal null. -/
theorem original_endpoint_initial_path (t : unitInterval) :
    perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p (0, t) =
      perfectOpenScalarNormalizedTerminalNull j r q hq n p t :=
  perfectOpenScalarNormalizedEndpointHomotopy_zero j r q hq n p t

/-- The final whole path retains the original canonical null after the complete fine delta. -/
theorem original_endpoint_final_path (t : unitInterval) :
    perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p (1, t) =
      (((perfectOpenScalarNormalizedFineDelta j r q hq n p).map (F).continuous).trans
        (perfectOpenScalarCanonicalNullPath j r q hq n p)) t :=
  perfectOpenScalarNormalizedEndpointHomotopy_one j r q hq n p t

/-- Both independent endpoint-comparison times fix the full original spatial boundary. -/
theorem original_endpoint_whole_boundary (s t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarNormalizedEndpointHomotopy j r q hq n p (s, t) z = (W).kBasepoint :=
  perfectOpenScalarNormalizedEndpointHomotopy_boundary j r q hq n p s t z hz

/-- Degree zero retains the same actual geometric Theta, complete null and both cancellations. -/
def originalConstructedDegreeZero (p0 : GenLoop (Fin 1)
    |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
    (subdivisionBasepoint V)) :
    (perfectOpenScalarNormalizedTerminalNull j r q hq 0 p0).Homotopy
      (((perfectOpenScalarNormalizedFineDelta j r q hq 0 p0).map
        (perfectOpenScalarCubeChangeWeak j 0).continuous).trans
          (perfectOpenScalarCanonicalNullPath j r q hq 0 p0)) :=
  perfectOpenScalarNormalizedEndpointHomotopy j r q hq 0 p0

end QuillenTest.ScalarCofiberSumCubeNormalization
