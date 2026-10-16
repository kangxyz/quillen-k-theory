/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarCofiberProjectionRealization

/-! Whole ordinary scalar triangle and the actual subdivided diagonal inclusion cylinder. -/
public section
noncomputable section
open AlgebraicGeometry.Scheme.Modules.Complex
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Quillen Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.Waldhausen.Additivity Quillen.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace QuillenTest.ScalarCofiberProjectionRealization
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- Both original triangle times survive the actual level-one homeomorphisms. -/
theorem original_whole_triangle (a t : unitInterval) (x : (perfectWaldhausen X).Delooping) :
    perfectOpenScalarProjectionRealizationTriangle j r q hq (a, (t, x)) =
      (perfectOpenNested j).coarse.smallModelDeloopingHomeomorph.symm
        ((perfectOpenScalarProjectionCompositionTrack j r q hq).level 1
          (a, (t, (perfectWaldhausen X).smallModelDeloopingHomeomorph x))) :=
  perfectOpenScalarProjectionRealizationTriangle_apply j r q hq a t x

/-- The actual subdivided diagonal inclusion face retains its complete ordinary cylinder. -/
theorem original_diagonal_subdivided (t : unitInterval)
    (x : |TheoremA.diagonalSSet
      (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|) :
    SSet.toTop.map (bisimplicialDiagonalIso (perfectOpenNested j).coarse).hom
        (realizationSimplicialHomotopy
          (normalizedMiddleTransformationHomotopy (perfectWaldhausen X) (perfectOpenNested j).coarse
            (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
            (QuotientRows.oneIdToZero (perfectOpenNested j).coarse)
            (perfectScalarConeProjectionNat X r)
            (perfectOpenScalarIdentityCofibrationSequence j)
            (perfectOpenScalarCofibrationSequence j r)
            (perfectScalarInclusionNat X r) (perfectScalarInclusionNat_openWeak j r q hq))
          (t, realizedDiagonalMap
            (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet (perfectWaldhausen X))) x)) =
      perfectOpenScalarInclusionRealizationHomotopy j r q hq
        (t, SSet.toTop.map (bisimplicialDiagonalIso (perfectWaldhausen X)).hom
          (realizedDiagonalMap
            (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet (perfectWaldhausen X))) x)) :=
  perfectOpenScalarInclusionDiagonalRealization j r q hq t _

end QuillenTest.ScalarCofiberProjectionRealization
