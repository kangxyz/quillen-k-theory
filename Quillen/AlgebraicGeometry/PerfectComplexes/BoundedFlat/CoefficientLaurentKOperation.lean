/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitKOperation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitTrack

/-!
# Original Laurent-unit K-operations under every coefficient map

The actual projection square and the actual pulled-back unit identify both complete
operations under arbitrary coefficient maps. Neither flatness nor quasi-compactness is
required for these original bounded-flat K-operation naturality equations.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The actual forward Laurent self-track operation on the original coefficient model. -/
def boundedFlatCoefficientLaurentKOperation (a : Under R) (n : ℕ) :=
  originalKSelfTrackOperation (boundedFlatPerfectWaldhausen (space (op P, a)))
    (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a)))
    (boundedFlatCoefficientLaurentUnitHomotopy P a) n

/-- The actual inverse-unit self-track operation on the same original projection. -/
def boundedFlatCoefficientInverseLaurentKOperation (a : Under R) (n : ℕ) :=
  originalKSelfTrackOperation (boundedFlatPerfectWaldhausen (space (op P, a)))
    (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a)))
    (boundedFlatPerfectUnitHomotopy (laurentProjection P a)
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right))⁻¹) n

/-- Every original coefficient map preserves the actual forward Laurent operation. -/
theorem boundedFlatCoefficientLaurentKOperation_naturality
    {a b : Under R} (u : a ⟶ b) (n : ℕ) :
    (boundedFlatPerfectKPullback (coefficientMap P ((laurentUnderFunctor R).map u))
      (n + 1)).comp (boundedFlatCoefficientLaurentKOperation P a n) =
      (boundedFlatCoefficientLaurentKOperation P b n).comp
        (boundedFlatPerfectKPullback (coefficientMap P u) n) := by
  unfold boundedFlatCoefficientLaurentKOperation boundedFlatCoefficientLaurentUnitHomotopy
  rw [boundedFlatPerfectUnitHomotopy_originalKOperation_postcomp,
    boundedFlatPerfectUnitHomotopy_originalKOperation_precomp,
    boundedFlatCoefficientLaurentUnit_coefficient]
  exact congrArg (fun f => originalKSelfTrackOperation
    (boundedFlatPerfectWaldhausen (space (op P, a)))
    (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj b)))
    (boundedFlatPerfectUnitHomotopy f
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit b.right))) n)
      (coefficientMap_naturality P (laurentUnderCoefficient R) u)

/-- Every original coefficient map preserves the literal inverse-unit operation as well. -/
theorem boundedFlatCoefficientInverseLaurentKOperation_naturality
    {a b : Under R} (u : a ⟶ b) (n : ℕ) :
    (boundedFlatPerfectKPullback (coefficientMap P ((laurentUnderFunctor R).map u))
      (n + 1)).comp (boundedFlatCoefficientInverseLaurentKOperation P a n) =
      (boundedFlatCoefficientInverseLaurentKOperation P b n).comp
        (boundedFlatPerfectKPullback (coefficientMap P u) n) := by
  unfold boundedFlatCoefficientInverseLaurentKOperation
  rw [boundedFlatPerfectUnitHomotopy_originalKOperation_postcomp,
    boundedFlatPerfectUnitHomotopy_originalKOperation_precomp, map_inv,
    boundedFlatCoefficientLaurentUnit_coefficient]
  exact congrArg (fun f => originalKSelfTrackOperation
    (boundedFlatPerfectWaldhausen (space (op P, a)))
    (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj b)))
    (boundedFlatPerfectUnitHomotopy f
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit b.right))⁻¹) n)
      (coefficientMap_naturality P (laurentUnderCoefficient R) u)

end Quillen.PerfectComplexes
