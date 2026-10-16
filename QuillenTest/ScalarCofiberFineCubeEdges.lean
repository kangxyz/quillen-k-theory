/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberFineCubeEdges

/-! Whole original fine paths, all four derived corners and the unchanged interpolation. -/
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
namespace QuillenTest.ScalarCofiberFineCubeEdges
local instance (X : Scheme.{u}) : HasBinaryCoproducts (Perfect X) :=
  Additivity.hasBinaryCoproducts (perfectWaldhausen X)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
    (subdivisionBasepoint (perfectWaldhausen X)))
local notation "V" => perfectWaldhausen X
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)

/-- Both the original chosen object and its actual quotient arrow are unchanged. -/
theorem original_zero_data :
    (V).zero = (W).zero ∧ QuotientRows.oneIdToZero V = QuotientRows.oneIdToZero W :=
  ⟨perfectOpenScalarFineZero_eq j, perfectOpenScalarFineZeroArrow_eq j⟩

/-- The fine identity track retains the whole old additivity formula. -/
theorem original_fine_identity (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarIdentityFineCubePath n p t z =
      SSet.toTop.map (bisimplicialDiagonalIso V).hom
        (subdividedBasedAdditivityHomotopy V V (𝟙 (𝟭 (Perfect X)))
          (QuotientRows.oneIdToZero V)
          (perfectScalarIdentityFineCofibrationSequence (X := X)) (t, p z)) := rfl

/-- The fine scalar track retains the original signed-cone cofibration sequence. -/
theorem original_fine_scalar (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarSequenceFineCubePath r n p t z =
      SSet.toTop.map (bisimplicialDiagonalIso V).hom
        (subdividedBasedAdditivityHomotopy V V (perfectScalarInclusionNat X r)
          (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r)
          (t, p z)) := rfl

/-- The entire fine identity edge maps to its original coarse edge. -/
theorem original_identity_image (t : unitInterval) :
    perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarIdentityFineCubePath n p t) =
      perfectOpenScalarCofiberCubeIdentityPath j r q hq n p t :=
  perfectOpenScalarIdentityFineCubePath_changeWeak j r q hq n p t

/-- The entire fine scalar edge maps to its original coarse edge. -/
theorem original_scalar_image (t : unitInterval) :
    perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarSequenceFineCubePath r n p t) =
      perfectOpenScalarCofiberCubeScalarPath j r q hq n p t :=
  perfectOpenScalarSequenceFineCubePath_changeWeak j r q hq n p t

/-- Corner 00 comes from the same actual whole fine edge. -/
theorem original_corner00 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivitySourceCube X (𝟙 (𝟭 (Perfect X))) (QuotientRows.oneIdToZero V)
      (perfectScalarIdentityFineCofibrationSequence (X := X)) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (0, 0) :=
  perfectOpenScalarFineCorner00 j r q hq n p

/-- Corner 01 comes from the same actual whole fine edge. -/
theorem original_corner01 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivityTargetCube X (𝟙 (𝟭 (Perfect X))) (QuotientRows.oneIdToZero V)
      (perfectScalarIdentityFineCofibrationSequence (X := X)) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (0, 1) :=
  perfectOpenScalarFineCorner01 j r q hq n p

/-- Corner 10 comes from the same actual whole fine edge. -/
theorem original_corner10 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivitySourceCube X (perfectScalarInclusionNat X r)
      (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (1, 0) :=
  perfectOpenScalarFineCorner10 j r q hq n p

/-- Corner 11 comes from the same actual whole fine edge. -/
theorem original_corner11 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
      (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (1, 1) :=
  perfectOpenScalarFineCorner11 j r q hq n p

/-- Both interpolation coordinates retain the accepted original oriented square. -/
theorem original_interpolation (a t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarFineCubeBoundaryHomotopy j r q hq n p (a, t) z =
      perfectOpenScalarCofiberCubeBoundaryHomotopy j r q hq n p (a, t) z :=
  perfectOpenScalarFineCubeBoundaryHomotopy_apply j r q hq n p a t z

/-- Every spatial boundary point stays fixed at independently varying interpolation times. -/
theorem original_full_boundary (a t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarFineCubeBoundaryHomotopy j r q hq n p (a, t) z = (W).kBasepoint :=
  perfectOpenScalarFineCubeBoundaryHomotopy_boundary j r q hq n p a t z hz

/-- Input degree zero preserves the entire original one-coordinate cube path. -/
theorem original_degree_zero
    (p₀ : GenLoop (Fin (0 + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      (subdivisionBasepoint V)) (t : unitInterval) :
    perfectOpenScalarCubeChangeWeak j 0 (perfectOpenScalarSequenceFineCubePath r 0 p₀ t) =
      perfectOpenScalarCofiberCubeScalarPath j r q hq 0 p₀ t :=
  perfectOpenScalarSequenceFineCubePath_changeWeak j r q hq 0 p₀ t

/-- The actual typed boundary comparison is the input needed by the fine return construction. -/
def original_typed_boundary :
    ((perfectOpenScalarFineCubeInclusionPath j r q hq n p).trans
      ((perfectOpenScalarSequenceFineCubePath r n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous)).Homotopy
      (((perfectOpenScalarIdentityFineCubePath n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous).trans
        (perfectOpenScalarFineCubeSumPath j r q hq n p)) :=
  perfectOpenScalarFineCubeBoundaryHomotopy j r q hq n p

end QuillenTest.ScalarCofiberFineCubeEdges
