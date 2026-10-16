/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarCofiberCanonicalFiberCube

/-! # Exact original scalar acyclic-to-fiber cube consumers -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.Waldhausen.Fibration
open scoped Topology Simplicial
universe u
namespace QuillenTest.ScalarCofiberCanonicalFiberCube
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
    (subdivisionBasepoint (perfectWaldhausen X)))
local notation "V" => perfectWaldhausen X
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N

/-- The whole original null lift equals the canonical fiber map, before taking any class. -/
theorem original_whole_cube :
    HomotopyFiber.genLoopNullLift (changeWeakMap N) (W).kBasepoint (V).kBasepoint
        (changeWeakMap_basepoint N) n
        (perfectOpenScalarCanonicalConeCube j r q hq n p)
        (perfectOpenScalarCanonicalNullPath j r q hq n p) =
      genLoopPostcomp (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
        (perfectOpenScalarCanonicalAcyclicCube j r q hq n p) :=
  perfectOpenScalarCanonicalFiberCube_eq j r q hq n p

/-- Projection keeps the actual public cone and its original fine inclusion. -/
theorem original_source_coordinate (z : Fin (n + 1) → unitInterval) :
    (perfectOpenScalarCanonicalFiberCube j r q hq n p z).val.1 =
      acyclicInclusionMap N (perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) :=
  perfectOpenScalarCanonicalFiberCube_source j r q hq n p z

/-- All original null times and spatial coordinates survive the source cast. -/
theorem original_null_times (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    (perfectOpenScalarCanonicalFiberCube j r q hq n p z).val.2 t =
      acyclicNullhomotopy N (t, perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) :=
  perfectOpenScalarCanonicalFiberCube_path j r q hq n p z t

/-- The original one-dimensional input has the full based fiber boundary. -/
theorem original_degree_zero_boundary
    (p0 : GenLoop (Fin 1)
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
      (subdivisionBasepoint (perfectWaldhausen X)))
    (z : Fin 1 → unitInterval) (hz : z ∈ Cube.boundary (Fin 1)) :
    perfectOpenScalarCanonicalFiberCube j r q hq 0 p0 z =
      HomotopyFiber.basepoint (changeWeakMap N) (W).kBasepoint (V).kBasepoint
        (changeWeakMap_basepoint N) :=
  (perfectOpenScalarCanonicalFiberCube j r q hq 0 p0).property z hz

end QuillenTest.ScalarCofiberCanonicalFiberCube
