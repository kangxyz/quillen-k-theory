/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberCubeReturn

/-! The exact fine return, moving terminal endpoint, complete homotopy and degree-zero boundary. -/
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
namespace QuillenTest.ScalarCofiberCubeReturn
local instance (X : Scheme.{u}) : HasBinaryCoproducts (Perfect X) :=
  Additivity.hasBinaryCoproducts (perfectWaldhausen X)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
    (subdivisionBasepoint (perfectWaldhausen X)))
local notation "V" => perfectWaldhausen X
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)

/-- The actual fine projection is reversed once before the complete scalar additivity edge. -/
theorem original_fine_return :
    perfectOpenScalarFineCubeReturn j r n p =
      (perfectOpenScalarFineProjectionCubePath j r n p).symm.trans
        (perfectOpenScalarSequenceFineCubePath r n p) := rfl

/-- Both old reversed edges and their original parentheses remain literal. -/
theorem original_terminal_word :
    perfectOpenScalarFineCubeTerminalWord j r q hq n p =
      (perfectOpenScalarFineCubeSumPath j r q hq n p).symm.trans
        ((perfectOpenScalarIdentityFineCubePath n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous).symm := rfl

/-- The terminal endpoint is the moving original cube, with no constant-cube replacement. -/
theorem original_moving_endpoint :
    perfectOpenScalarFineCubeTerminalWord j r q hq n p 1 =
      perfectOpenScalarCubeChangeWeak j n
        (scalarFineAdditivitySourceCube X (𝟙 (𝟭 (Perfect X))) (QuotientRows.oneIdToZero V)
          (perfectScalarIdentityFineCofibrationSequence (X := X)) n p) :=
  (perfectOpenScalarFineCubeTerminalWord j r q hq n p).target

/-- The exact returned data identifies the whole inverse inclusion/projection word. -/
def original_complete_homotopy :
    (((perfectOpenScalarFineCubeReturn j r n p).map
      (perfectOpenScalarCubeChangeWeak j n).continuous).trans
        (perfectOpenScalarFineCubeTerminalWord j r q hq n p)).Homotopy
      ((perfectOpenScalarFineCubeInclusionPath j r q hq n p).trans
        ((perfectOpenScalarFineProjectionCubePath j r n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous)).symm :=
  perfectOpenScalarCubeReturnHomotopy j r q hq n p

/-- Every intermediate homotopy/path pair retains every original boundary coordinate. -/
theorem original_whole_boundary (a t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarCubeReturnHomotopy j r q hq n p (a, t) z = (W).kBasepoint :=
  perfectOpenScalarCubeReturnHomotopy_boundary j r q hq n p a t z hz

/-- The one-coordinate input already retains the complete signed return homotopy boundary. -/
theorem original_degree_zero
    (p₀ : GenLoop (Fin (0 + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      (subdivisionBasepoint V)) (a t : unitInterval) (z : Fin (0 + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (0 + 1))) :
    perfectOpenScalarCubeReturnHomotopy j r q hq 0 p₀ (a, t) z = (W).kBasepoint :=
  perfectOpenScalarCubeReturnHomotopy_boundary j r q hq 0 p₀ a t z hz

end QuillenTest.ScalarCofiberCubeReturn
