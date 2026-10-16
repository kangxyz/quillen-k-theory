/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarCofiberProjectionTrack
public import Quillen.Waldhausen.Additivity.EndpointTransformationSquare
public import Quillen.Topology.Realization.HomotopySquare

/-!
# The whole original scalar inclusion diagonal cylinder

The scalar additivity square's actual normalized inclusion cylinder agrees through the original
bisimplicial diagonal isomorphisms with its ordinary weak-transformation cylinder. The identity
retains every simplicial input, and its realization retains the full original time and source.
It uses the same canonical endpoint rebases as the scalar inclusion/projection sequence.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.Waldhausen.Additivity Quillen.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => perfectWaldhausen X
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "hF" => changeWeak_exact (perfectOpenNested j)
local notation "hM" =>
  Additivity.IsCofibrationSequence.exactG (perfectOpenScalarCofibrationSequence j r)

/-- The exact normalized inclusion edge of the scalar additivity square, before realization. -/
theorem perfectOpenScalarInclusionDiagonalCylinder :
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
            (perfectScalarInclusionNat_openWeak j r q hq)) := by
  ext n z
  apply Subtype.ext
  rfl

/-- The whole old diagonal cylinder matches the ordinary inclusion through the actual isos. -/
theorem perfectOpenScalarInclusionDiagonalRealization
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
  realizationSimplicialHomotopy_square _ _ _ _
    (perfectOpenScalarInclusionDiagonalCylinder j r q hq) t x

end Quillen.PerfectComplexes
