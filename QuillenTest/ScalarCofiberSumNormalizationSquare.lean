/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberSumNormalizationSquare

/-! Exact old alpha, all four complete faces, whole zero and actual fine/coarse cylinders. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Opposite MonoidalCategory Quillen Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u
namespace QuillenTest.ScalarCofiberSumNormalizationSquare
local instance (X : Scheme.{u}) : HasBinaryCoproducts (Perfect X) :=
  Additivity.hasBinaryCoproducts (perfectWaldhausen X)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => perfectWaldhausen X
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "S" => OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V

/-- The original separated family still contains the actual old quotient-first transformation. -/
theorem original_alpha_family :
    perfectOpenScalarSeparatedSumFamily j r q hq =
      normalizedSumTransformationFamily V W (𝟙 (𝟭 (Perfect X)))
        (perfectScalarInclusionNat X r) (QuotientRows.oneIdToZero W)
        (perfectScalarConeProjectionNat X r)
        (perfectOpenScalarIdentityCofibrationSequence j)
        (perfectOpenScalarCofibrationSequence j r) (𝟙 (𝟭 (Perfect X)))
        (perfectOpenScalarZeroToCone j r q hq) :=
  perfectOpenScalarSeparatedSumFamily_eq j r q hq

/-- The entire original vertical zero cylinder is retained. -/
theorem original_simplicial_vertical_zero :
    SSet.ι₀ ≫ perfectOpenScalarSumNormalizationSquareMap j r q hq =
      (perfectOpenScalarSumDiagonalHomotopy j r q hq).h :=
  perfectOpenScalarSumNormalizationSquareMap_vertical_zero j r q hq

/-- The entire original vertical one cylinder is retained. -/
theorem original_simplicial_vertical_one :
    SSet.ι₁ ≫ perfectOpenScalarSumNormalizationSquareMap j r q hq =
      (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq).h :=
  perfectOpenScalarSumNormalizationSquareMap_vertical_one j r q hq

/-- The entire original horizontal zero cylinder is retained. -/
theorem original_simplicial_horizontal_zero :
    (SSet.ι₀ ▷ Δ[1]) ≫ perfectOpenScalarSumNormalizationSquareMap j r q hq =
      (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j).h :=
  perfectOpenScalarSumNormalizationSquareMap_horizontal_zero j r q hq

/-- The entire original horizontal one cylinder is retained. -/
theorem original_simplicial_horizontal_one :
    (SSet.ι₁ ▷ Δ[1]) ≫ perfectOpenScalarSumNormalizationSquareMap j r q hq =
      (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q hq).h :=
  perfectOpenScalarSumNormalizationSquareMap_horizontal_one j r q hq

/-- Every cut in each direction fixes the actual full chosen-zero grid. -/
theorem original_simplicial_zero :
    ((SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) ≫
        perfectOpenScalarSumNormalizationSquareMap j r q hq =
      CartesianMonoidalCategory.fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) :=
  perfectOpenScalarSumNormalizationSquareMap_fixed_zero j r q hq

/-- Both actual realization-cylinder inverses retain their original order. -/
theorem original_two_inverse_formula (t s : unitInterval) (x : |TheoremA.diagonalSSet S|) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (s, x)) =
      SSet.toTop.map (perfectOpenScalarSumNormalizationSquareMap j r q hq)
        ((realizationCylinderIso (TheoremA.diagonalSSet S ⊗ Δ[1])).inv
          ((realizationCylinderIso (TheoremA.diagonalSSet S)).inv
            (x, ULift.up s), ULift.up t)) :=
  perfectOpenScalarSumNormalizationRealizationSquare_apply j r q hq t s x

/-- Every input of the realized vertical zero face remains explicit. -/
theorem original_continuous_vertical_zero (t : unitInterval) (x : |TheoremA.diagonalSSet S|) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (0, (t, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarSumDiagonalHomotopy j r q hq) (t, x) :=
  perfectOpenScalarSumNormalizationRealizationSquare_vertical_zero j r q hq t x

/-- Every input of the realized vertical one face remains explicit. -/
theorem original_continuous_vertical_one (t : unitInterval) (x : |TheoremA.diagonalSSet S|) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (1, (t, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
      (t, x) :=
  perfectOpenScalarSumNormalizationRealizationSquare_vertical_one j r q hq t x

/-- Every input of the realized horizontal zero face remains explicit. -/
theorem original_continuous_horizontal_zero (t : unitInterval) (x : |TheoremA.diagonalSSet S|) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (0, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j) (t, x) :=
  perfectOpenScalarSumNormalizationRealizationSquare_horizontal_zero j r q hq t x

/-- Every input of the realized horizontal one face remains explicit. -/
theorem original_continuous_horizontal_one (t : unitInterval) (x : |TheoremA.diagonalSSet S|) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (1, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q
      hq) (t, x) :=
  perfectOpenScalarSumNormalizationRealizationSquare_horizontal_one j r q hq t x

/-- The complete original two-time zero surface is retained. -/
theorem original_continuous_zero (t s : unitInterval) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq
      (t, (s, subdivisionBasepoint V)) = realizationPoint (diagonalZeroVertex W) :=
  perfectOpenScalarSumNormalizationRealizationSquare_fixed_zero j r q hq t s

/-- The entire fine zero cylinder has exactly its original change-weak image. -/
theorem original_zero_cylinder_changeWeak :
    (perfectOpenScalarZeroThetaDiagonalHomotopy j).h ≫
        TheoremA.diagonalMap (bisimplicialSSetMap (V).cof (V).weq
          (changeWeak_exact (perfectOpenNested j))) =
      (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j).h :=
  perfectOpenScalarZeroThetaDiagonalHomotopy_changeWeak j

/-- The full fine zero zero track retains every original time. -/
theorem original_zero_fine_zero (t : unitInterval) :
    realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)
      (t, subdivisionBasepoint V) = realizationPoint (diagonalZeroVertex V) :=
  perfectOpenScalarZeroThetaDiagonalHomotopy_fixed_zero j t

/-- Both original time and input survive ordinary zero-normalization naturality. -/
theorem original_zero_ordinary_changeWeak (t : unitInterval)
    (x : |TheoremA.diagonalSSet S|) :
    deloopingMap (changeWeak_exact (perfectOpenNested j))
        (SSet.toTop.map (bisimplicialDiagonalIso V).hom
          (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)
            (t, x))) =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy
          (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j) (t, x)) :=
  perfectOpenScalarZeroThetaRealization_changeWeak j t x

/-- The entire fine cone cylinder has exactly its original change-weak image. -/
theorem original_cone_cylinder_changeWeak :
    (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq).h ≫
        TheoremA.diagonalMap (bisimplicialSSetMap (V).cof (V).weq
          (changeWeak_exact (perfectOpenNested j))) =
      (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q hq).h :=
  perfectOpenScalarConeThetaDiagonalHomotopy_changeWeak j r q hq

/-- The full fine cone zero track retains every original time. -/
theorem original_cone_fine_zero (t : unitInterval) :
    realizationSimplicialHomotopy (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)
      (t, subdivisionBasepoint V) = realizationPoint (diagonalZeroVertex V) :=
  perfectOpenScalarConeThetaDiagonalHomotopy_fixed_zero j r q hq t

/-- Both original time and input survive ordinary cone-normalization naturality. -/
theorem original_cone_ordinary_changeWeak (t : unitInterval)
    (x : |TheoremA.diagonalSSet S|) :
    deloopingMap (changeWeak_exact (perfectOpenNested j))
        (SSet.toTop.map (bisimplicialDiagonalIso V).hom
          (realizationSimplicialHomotopy (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)
            (t, x))) =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy
          (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q hq) (t, x)) :=
  perfectOpenScalarConeThetaRealization_changeWeak j r q hq t x

/-- Every spatial boundary of an arbitrary original subdivision cube fixes both square times. -/
theorem original_cube_boundary (n : ℕ)
    (p : GenLoop (Fin (n + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
      (subdivisionBasepoint (perfectWaldhausen X)))
    (t s : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (s, p z)) =
      realizationPoint (diagonalZeroVertex W) := by
  exact (congrArg (fun x : |TheoremA.diagonalSSet S| ↦
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (s, x)))
    (p.property z hz)).trans
      (perfectOpenScalarSumNormalizationRealizationSquare_fixed_zero j r q hq t s)

/-- One-coordinate inputs retain the same complete two-time boundary. -/
theorem original_degree_zero
    (p : GenLoop (Fin (0 + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
      (subdivisionBasepoint (perfectWaldhausen X)))
    (t s : unitInterval) (z : Fin (0 + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (0 + 1))) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (s, p z)) =
      realizationPoint (diagonalZeroVertex W) :=
  original_cube_boundary j r q hq 0 p t s z hz

end QuillenTest.ScalarCofiberSumNormalizationSquare
