/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatStableKZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassNegativeGroups
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSquare

/-!
# The original first Bass cokernel in stable coordinates

The unchanged original polynomial difference is transported along the actual original K-zero
comparison. Both polynomial charts and the literal Laurent quotient projection are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- The difference of the two original raw stable polynomial-to-Laurent maps. -/
def boundedFlatBassStableDifference (R : CommRingCat.{u}) :=
  biprod.desc ((stableHomotopyFunctor 0).map (boundedFlatPerfectPrespectrumMap (laurentPlus R)))
    (-((stableHomotopyFunctor 0).map (boundedFlatPerfectPrespectrumMap (laurentMinus R))))

/-- Original perfect K-zero and the actual raw stable chart difference give the same cokernel. -/
def boundedFlatBassKZeroCokernelIso (R : CommRingCat.{u}) :
    Quillen.Bass.negativeK R 1 ≅ cokernel (boundedFlatBassStableDifference R) :=
  cokernel.mapIso (Quillen.Bass.polynomialDifference Quillen.Bass.affineKZeroFunctor R)
    (boundedFlatBassStableDifference R)
    (biprod.mapIso (boundedFlatAffineStableKZeroIso (.of (Polynomial R)))
      (boundedFlatAffineStableKZeroIso (.of (Polynomial R))))
    (boundedFlatAffineStableKZeroIso (.of (LaurentPolynomial R))) (by
      apply biprod.hom_ext'
      · simp only [Quillen.Bass.polynomialDifference, biprod.inl_desc_assoc,
          biprod.mapIso_hom, biprod.inl_map_assoc, boundedFlatBassStableDifference,
          biprod.inl_desc]
        exact (boundedFlatAffineStableKZeroIso_naturality (Quillen.Bass.plus.app R)).symm
      · simp only [Quillen.Bass.polynomialDifference, biprod.inr_desc_assoc,
          biprod.mapIso_hom, biprod.inr_map_assoc, boundedFlatBassStableDifference,
          biprod.inr_desc, Preadditive.neg_comp, Preadditive.comp_neg]
        exact congrArg Neg.neg
          (boundedFlatAffineStableKZeroIso_naturality (Quillen.Bass.minus.app R)).symm)

/-- The actual original Laurent quotient projection is preserved by the stable-coordinate iso. -/
@[reassoc]
theorem boundedFlatBassKZeroCokernelIso_π (R : CommRingCat.{u}) :
    Quillen.Bass.negativeKπ R 0 ≫ (boundedFlatBassKZeroCokernelIso R).hom =
      (boundedFlatAffineStableKZeroIso (.of (LaurentPolynomial R))).hom ≫
        cokernel.π (boundedFlatBassStableDifference R) := by
  exact cokernel.π_desc _ _ _

end Quillen.PerfectComplexes
