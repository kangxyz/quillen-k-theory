/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberSequenceMap
public import Quillen.Waldhausen.Additivity.BasedTransformationSquare

/-! # The literal scalar map of full based-additivity squares

The accepted identity-to-scalar sequence map specializes the original subdivided full square.
Its four entire faces retain both original additivity paths, the rebased inclusion cylinder,
and the actual quotient-first normalized zero-to-cone sum cylinder. Both continuous times fix
the original chosen zero. Projection/null alignment and the signed fiber comparison are separate.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes

local instance scalarAdditivityCoproducts (X : Scheme.{u}) : HasBinaryCoproducts (Perfect X) :=
  Additivity.hasBinaryCoproducts (perfectWaldhausen X)

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The whole actual normalized inclusion cylinder on the ordinary diagonal. -/
def perfectOpenScalarInclusionDiagonalHomotopy :
    SSet.Homotopy
      (TheoremA.diagonalMap (bisimplicialSSetMap (perfectWaldhausen X).cof
        (perfectWaldhausen X).weq (perfectOpenScalarIdentityCofibrationSequence j).exactG.rebase))
      (TheoremA.diagonalMap (bisimplicialSSetMap (perfectWaldhausen X).cof
        (perfectWaldhausen X).weq (perfectOpenScalarCofibrationSequence j r).exactG.rebase)) :=
  normalizedMiddleTransformationHomotopy (perfectWaldhausen X) (perfectOpenNested j).coarse
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (perfectScalarInclusionNat X r) (perfectScalarInclusionNat_openWeak j r q hq)

/-- The whole actual quotient-first normalized zero-to-cone and identity sum cylinder. -/
def perfectOpenScalarSumDiagonalHomotopy :
    SSet.Homotopy
      (TheoremA.diagonalMap (normalizedSumMap (perfectWaldhausen X) (perfectOpenNested j).coarse
        (perfectOpenScalarIdentityCofibrationSequence j).exactH
        (perfectOpenScalarIdentityCofibrationSequence j).exactF))
      (TheoremA.diagonalMap (normalizedSumMap (perfectWaldhausen X) (perfectOpenNested j).coarse
        (perfectOpenScalarCofibrationSequence j r).exactH
        (perfectOpenScalarCofibrationSequence j r).exactF)) :=
  normalizedSumTransformationHomotopy (perfectWaldhausen X) (perfectOpenNested j).coarse
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (Perfect X))) (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K)
      (perfectOpenScalarZeroToCone j r q hq) (perfectOpenScalarZeroToCone_weak j r q hq)

/-- The literal full square at the original identity-to-scalar sequence map. -/
def perfectOpenScalarBasedAdditivitySquare :
    C(unitInterval × (unitInterval × |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙
      bisimplicialSSet (perfectWaldhausen X))|), |TheoremA.diagonalSSet (bisimplicialSSet
      (perfectOpenNested j).coarse)|) :=
  subdividedBasedAdditivityTransformationSquare (perfectWaldhausen X) (perfectOpenNested j).coarse
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq)

/-- The construction uses the exact original transformations and the complete old pasting. -/
theorem perfectOpenScalarBasedAdditivitySquare_eq :
    perfectOpenScalarBasedAdditivitySquare j r q hq =
      subdividedBasedAdditivityTransformationSquare (perfectWaldhausen X) (perfectOpenNested
        j).coarse
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) := rfl

/-- The entire transformation-zero face is the specified identity-sequence additivity path. -/
theorem perfectOpenScalarBasedAdditivitySquare_transformation_zero (s : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen
      X))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (0, (s, x)) =
      subdividedBasedAdditivityHomotopy (perfectWaldhausen X) (perfectOpenNested j).coarse (𝟙 (𝟭
        (Perfect X))) (QuotientRows.oneIdToZero (perfectOpenNested j).coarse)
        (perfectOpenScalarIdentityCofibrationSequence j) (s, x) :=
  subdividedBasedAdditivityTransformationSquare_transformation_zero (perfectWaldhausen X)
    (perfectOpenNested j).coarse
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) s x

/-- The entire transformation-one face is the specified actual scalar-sequence additivity path. -/
theorem perfectOpenScalarBasedAdditivitySquare_transformation_one (s : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen
      X))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (1, (s, x)) =
      subdividedBasedAdditivityHomotopy (perfectWaldhausen X) (perfectOpenNested j).coarse
        (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
        (perfectOpenScalarCofibrationSequence j r) (s, x) :=
  subdividedBasedAdditivityTransformationSquare_transformation_one (perfectWaldhausen X)
    (perfectOpenNested j).coarse
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) s x

/-- The complete initial face keeps the normalized inclusion on actual first-half restriction. -/
theorem perfectOpenScalarBasedAdditivitySquare_additivity_zero (t : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen
      X))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (t, (0, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarInclusionDiagonalHomotopy j r q hq)
        (t, (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet
          (perfectWaldhausen X)))) x) :=
  subdividedBasedAdditivityTransformationSquare_additivity_zero (perfectWaldhausen X)
    (perfectOpenNested j).coarse
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) t x

/-- The complete terminal face keeps both half restrictions and the quotient-first normalization. -/
theorem perfectOpenScalarBasedAdditivitySquare_additivity_one (t : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen
      X))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (t, (1, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarSumDiagonalHomotopy j r q hq) (t, x) :=
  subdividedBasedAdditivityTransformationSquare_additivity_one (perfectWaldhausen X)
    (perfectOpenNested j).coarse
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) t x

/-- Both original continuous times fix the actual subdivided zero vertex. -/
theorem perfectOpenScalarBasedAdditivitySquare_fixed_zero (t s : unitInterval) :
    perfectOpenScalarBasedAdditivitySquare j r q hq
      (t, (s, subdivisionBasepoint (perfectWaldhausen X))) =
        realizationPoint (diagonalZeroVertex (perfectOpenNested j).coarse) :=
  subdividedBasedAdditivityTransformationSquare_fixed_zero (perfectWaldhausen X) (perfectOpenNested
    j).coarse
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (Perfect X))) (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) t s

end Quillen.PerfectComplexes
