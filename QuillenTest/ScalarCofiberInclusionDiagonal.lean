/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarCofiberInclusionDiagonal

/-! The entire original inclusion cylinder, its ordinary realization, and subdivision input. -/
public section
noncomputable section
open AlgebraicGeometry.Scheme.Modules.Complex
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry MonoidalCategory Quillen Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.Waldhausen.Additivity Quillen.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace QuillenTest.ScalarCofiberInclusionDiagonal
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

local notation "V" => perfectWaldhausen X
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "hF" => changeWeak_exact (perfectOpenNested j)
local notation "hM" =>
  Additivity.IsCofibrationSequence.exactG (perfectOpenScalarCofibrationSequence j r)

/-- The entire original simplicial cylinder, with the actual endpoint normalizations. -/
theorem original_whole_cylinder :
    (normalizedMiddleTransformationHomotopy V W
      (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
      (QuotientRows.oneIdToZero W) (perfectScalarConeProjectionNat X r)
      (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
      (perfectScalarInclusionNat X r) (perfectScalarInclusionNat_openWeak j r q hq)).h ≫
        (bisimplicialDiagonalIso W).hom =
      (bisimplicialDiagonalIso V).hom ▷ Δ[1] ≫
        weakNaturalTransformationCylinder V W (hF).rebase (hM).rebase
          (normalizedWeakTransformation hF hM (perfectScalarInclusionNat X r))
          (normalizedWeakTransformation_weak hF hM (perfectScalarInclusionNat X r)
            (perfectScalarInclusionNat_openWeak j r q hq)) :=
  perfectOpenScalarInclusionDiagonalCylinder j r q hq

/-- Every ordinary input and the full inclusion time survive the actual diagonal maps. -/
theorem original_ordinary_cylinder
    (t : unitInterval) (x : |TheoremA.diagonalSSet (bisimplicialSSet V)|) :
    SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy
          (normalizedMiddleTransformationHomotopy V W
            (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
            (QuotientRows.oneIdToZero W) (perfectScalarConeProjectionNat X r)
            (perfectOpenScalarIdentityCofibrationSequence j)
            (perfectOpenScalarCofibrationSequence j r)
            (perfectScalarInclusionNat X r) (perfectScalarInclusionNat_openWeak j r q hq))
          (t, x)) =
      perfectOpenScalarInclusionRealizationHomotopy j r q hq
        (t, SSet.toTop.map (bisimplicialDiagonalIso V).hom x) :=
  perfectOpenScalarInclusionDiagonalRealization j r q hq t x

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

end QuillenTest.ScalarCofiberInclusionDiagonal
