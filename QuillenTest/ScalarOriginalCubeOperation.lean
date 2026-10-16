/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarOriginalCubeOperation

/-! # The original scalar cube and its actual operation, including degree zero -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.PerfectComplexes Quillen.Waldhausen
open Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace QuillenTest.ScalarOriginalCubeOperation
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The original scalar and cube coordinates are independent and literal. -/
theorem original_cube (n : ℕ) (p : GenLoop (Fin (n + 1))
    (perfectWaldhausen X).Delooping (perfectWaldhausen X).kBasepoint)
    (s : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCubePath j r q hq n p s z =
      weakNaturalTransformationRealizationHomotopy (perfectWaldhausen X)
        (perfectOpenWeakWaldhausen j) (changeWeak_exact (perfectOpenNested j))
        (changeWeak_exact (perfectOpenNested j)) (perfectGlobalScalar X r)
        (perfectGlobalScalar_openWeak j r q hq) (s, p z) :=
  perfectOpenScalarCubePath_apply j r q hq n p s z

/-- The entire actual path uses the same source equality at both endpoints. -/
theorem original_cast_path (n : ℕ) (p : GenLoop (Fin (n + 1))
    (perfectWaldhausen X).Delooping (perfectWaldhausen X).kBasepoint) :
    ((perfectOpenScalarCubePath j r q hq n p).map
      (genLoopPostcompContinuousMap
        (perfectOpenWeakWaldhausen j).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
        (perfectOpenWeakWaldhausen j).smallModelDeloopingHomeomorph_basepoint).continuous).cast
          (perfectOpenScalarCubePath_smallModel_endpoint j r q hq n p).symm
          (perfectOpenScalarCubePath_smallModel_endpoint j r q hq n p).symm =
      (perfectOpenScalarOriginalHomotopy j r q hq).genLoopPath 1
        (genLoopPostcomp (perfectWaldhausen X).smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
          (perfectWaldhausen X).smallModelDeloopingHomeomorph_basepoint p) :=
  perfectOpenScalarCubePath_smallModel j r q hq n p

/-- Every original degree keeps the single level-one inverse. -/
theorem original_degree (n : ℕ) (p : GenLoop (Fin (n + 1))
    (perfectWaldhausen X).Delooping (perfectWaldhausen X).kBasepoint) :
    originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarOriginalHomotopy j r q hq) n (⟦p⟧ : (perfectWaldhausen X).K n) =
      (genLoopSelfTrackClass n
        (genLoopPostcomp (changeWeakMap (perfectOpenNested j))
          (changeWeakMap_basepoint (perfectOpenNested j)) p)
        (perfectOpenScalarCubePath j r q hq n p))⁻¹ :=
  perfectOpenScalarOriginalKOperation_cube j r q hq n p

/-- Degree zero needs only the supplied actual loop, with no input additivity assertion. -/
theorem original_degree_zero (p : GenLoop (Fin 1)
    (perfectWaldhausen X).Delooping (perfectWaldhausen X).kBasepoint) :
    originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarOriginalHomotopy j r q hq) 0 (⟦p⟧ : (perfectWaldhausen X).K 0) =
      (genLoopSelfTrackClass 0
        (genLoopPostcomp (changeWeakMap (perfectOpenNested j))
          (changeWeakMap_basepoint (perfectOpenNested j)) p)
        (perfectOpenScalarCubePath j r q hq 0 p))⁻¹ :=
  perfectOpenScalarOriginalKOperation_cube j r q hq 0 p

end QuillenTest.ScalarOriginalCubeOperation
