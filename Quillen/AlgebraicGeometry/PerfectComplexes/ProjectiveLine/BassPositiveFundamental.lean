/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BassPositiveMayerVietoris

/-! # The original positive Bass fundamental row on perfect K-groups

For every commutative ring, including zero, the row in degree `n + 1` is
`1 → K(Spec R) → K(Spec R[T]) × K(Spec R[T]) → K(Spec R[T,T⁻¹]) → K(Spec R) → 1`.
The first arrow is the original polynomial coefficient pair, the next is
original positive Laurent restriction times inverse negative restriction,
and the last is the first O-coordinate of the original MV boundary through
the same native Phi equivalence. The transported boundary has exactly the
anti-diagonal coefficient image. The final group has degree `n`.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine FlasqueTwoSummands

local instance (Y : Scheme.{u}) (n : ℕ) : CommGroup (PerfectK Y n) :=
  Waldhausen.Additivity.KCommGroup (perfectWaldhausen Y) n

variable (R : CommRingCat.{u})

/-- The original polynomial coefficient extension in each of the two chart factors. -/
def polynomialCoefficientPair (n : ℕ) : PerfectK (Spec R) n →*
    PerfectK (Spec (.of (Polynomial R))) n × PerfectK (Spec (.of (Polynomial R))) n :=
  (polynomialCoefficientKMap R n).prod (polynomialCoefficientKMap R n)

/-- Both actual native Phi chart restrictions factor through the product of its coefficients. -/
theorem affineRestrictionPair_Phi (n : ℕ) (a b : PerfectK (Spec R) n) :
    affineRestrictionPair R n (nativeGlobalTwoSummandKEquiv (affineBase R) n (a, b)) =
      polynomialCoefficientPair R n (a * b) := by
  apply Prod.ext
  · exact affineNativeChart_Phi R true n a b
  · exact affineNativeChart_Phi R false n a b

/-- Actual zero evaluation proves injectivity of the first coefficient pair. -/
theorem polynomialCoefficientPair_injective (n : ℕ) :
    Function.Injective (polynomialCoefficientPair R n) := by
  intro a b h
  exact polynomialCoefficientKMap_injective R n (congrArg Prod.fst h)

/-- The original native Phi equivalence identifies the MV restriction image with coefficients. -/
theorem affineRestrictionPair_range_eq_coefficientPair (n : ℕ) :
    (affineRestrictionPair R n).range = (polynomialCoefficientPair R n).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let e := nativeGlobalTwoSummandKEquiv (affineBase R) n
    let c := e.symm y
    refine ⟨c.1 * c.2, ?_⟩
    calc
      _ = affineRestrictionPair R n (e c) :=
        (affineRestrictionPair_Phi R n c.1 c.2).symm
      _ = affineRestrictionPair R n y := congrArg (affineRestrictionPair R n)
        (e.apply_symm_apply y)
  · rintro ⟨y, rfl⟩
    refine ⟨nativeGlobalTwoSummandKEquiv (affineBase R) n (y, 1), ?_⟩
    simpa only [mul_one] using affineRestrictionPair_Phi R n y 1

/-- Original MV boundary in the same O, O(-1) native coefficient coordinates. -/
def connectingCoefficients (n : ℕ) :
    PerfectK (Spec (.of (LaurentPolynomial R))) (n + 1) →*
      PerfectK (Spec R) n × PerfectK (Spec R) n :=
  (nativeGlobalTwoSummandKEquiv (affineBase R) n).symm.toMonoidHom.comp
    (laurentProjectiveConnecting R n)

/-- The final Bass boundary is the first O-coordinate of the original transported MV boundary. -/
def positiveBassBoundary (n : ℕ) :
    PerfectK (Spec (.of (LaurentPolynomial R))) (n + 1) →* PerfectK (Spec R) n :=
  (MonoidHom.fst _ _).comp (connectingCoefficients R n)

/-- The boundary coordinates multiply to one, by actual chart restriction and evaluation. -/
theorem connectingCoefficients_product_eq_one (n : ℕ)
    (x : PerfectK (Spec (.of (LaurentPolynomial R))) (n + 1)) :
    (connectingCoefficients R n x).1 * (connectingCoefficients R n x).2 = 1 := by
  let e := nativeGlobalTwoSummandKEquiv (affineBase R) n
  let y := laurentProjectiveConnecting R n x
  let c := connectingCoefficients R n x
  have hy : y ∈ (affineRestrictionPair R n).ker := by
    rw [← (affine_positiveExactSequence R n).2.2]
    exact ⟨x, rfl⟩
  have hpair : polynomialCoefficientPair R n (c.1 * c.2) = 1 := by
    calc
      _ = affineRestrictionPair R n (e c) :=
        (affineRestrictionPair_Phi R n c.1 c.2).symm
      _ = affineRestrictionPair R n y := congrArg (affineRestrictionPair R n)
        (e.apply_symm_apply y)
      _ = 1 := hy
  exact polynomialCoefficientKMap_injective R n
    ((congrArg Prod.fst hpair).trans (map_one (polynomialCoefficientKMap R n)).symm)

/-- The original boundary is literally anti-diagonal in the same native Phi coordinates. -/
theorem connectingCoefficients_antiDiagonal (n : ℕ)
    (x : PerfectK (Spec (.of (LaurentPolynomial R))) (n + 1)) :
    connectingCoefficients R n x =
      (positiveBassBoundary R n x, (positiveBassBoundary R n x)⁻¹) := by
  apply Prod.ext
  · rfl
  · change (connectingCoefficients R n x).2 = ((connectingCoefficients R n x).1)⁻¹
    calc
      _ = ((connectingCoefficients R n x).1)⁻¹ *
          ((connectingCoefficients R n x).1 * (connectingCoefficients R n x).2) := by
        rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = ((connectingCoefficients R n x).1)⁻¹ := by
        rw [connectingCoefficients_product_eq_one, mul_one]

/-- The scalar boundary has the same kernel as the original projective-line boundary. -/
theorem positiveBassBoundary_eq_one_iff (n : ℕ)
    (x : PerfectK (Spec (.of (LaurentPolynomial R))) (n + 1)) :
    positiveBassBoundary R n x = 1 ↔ laurentProjectiveConnecting R n x = 1 := by
  constructor
  · intro hx
    have hc : connectingCoefficients R n x = 1 := by
      rw [connectingCoefficients_antiDiagonal, hx, inv_one]
      rfl
    let e := nativeGlobalTwoSummandKEquiv (affineBase R) n
    have h := congrArg e hc
    change e (e.symm (laurentProjectiveConnecting R n x)) = e 1 at h
    simpa only [MulEquiv.apply_symm_apply, map_one] using h
  · intro hx
    change ((nativeGlobalTwoSummandKEquiv (affineBase R) n).symm
      (laurentProjectiveConnecting R n x)).1 = 1
    rw [hx, map_one]
    rfl

theorem positiveBassBoundary_ker (n : ℕ) :
    (positiveBassBoundary R n).ker = (laurentProjectiveConnecting R n).ker := by
  ext x
  exact positiveBassBoundary_eq_one_iff R n x

/-- Exactness at the polynomial pair in the positive Bass row. -/
theorem range_coefficientPair_eq_ker_laurentDifference (n : ℕ) :
    (polynomialCoefficientPair R (n + 1)).range = (laurentDifference R (n + 1)).ker := by
  rw [← affineRestrictionPair_range_eq_coefficientPair]
  exact (affine_positiveExactSequence R n).1

/-- Exactness at the original Laurent group in the positive Bass row. -/
theorem range_laurentDifference_eq_ker_positiveBassBoundary (n : ℕ) :
    (laurentDifference R (n + 1)).range = (positiveBassBoundary R n).ker := by
  rw [positiveBassBoundary_ker]
  exact (affine_positiveExactSequence R n).2.1

/-- Every anti-diagonal coefficient class is hit by the original MV boundary. -/
theorem positiveBassBoundary_surjective (n : ℕ) :
    Function.Surjective (positiveBassBoundary R n) := by
  intro a
  let e := nativeGlobalTwoSummandKEquiv (affineBase R) n
  have hz : e (a, a⁻¹) ∈ (affineRestrictionPair R n).ker := by
    change affineRestrictionPair R n
      (nativeGlobalTwoSummandKEquiv (affineBase R) n (a, a⁻¹)) = 1
    rw [affineRestrictionPair_Phi, mul_inv_cancel, map_one]
  have hm : e (a, a⁻¹) ∈ (laurentProjectiveConnecting R n).range := by
    rw [(affine_positiveExactSequence R n).2.2]
    exact hz
  obtain ⟨x, hx⟩ := hm
  refine ⟨x, ?_⟩
  change (e.symm (laurentProjectiveConnecting R n x)).1 = a
  rw [hx, MulEquiv.symm_apply_apply]

/-- The transported original boundary image is exactly the anti-diagonal coefficient factor. -/
theorem connectingCoefficients_range (n : ℕ) :
    Set.range (connectingCoefficients R n) =
      {c : PerfectK (Spec R) n × PerfectK (Spec R) n | c.2 = c.1⁻¹} := by
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    have h := congrArg Prod.snd (connectingCoefficients_antiDiagonal R n x)
    exact h
  · intro hc
    obtain ⟨x, hx⟩ := positiveBassBoundary_surjective R n c.1
    refine ⟨x, ?_⟩
    calc
      _ = (positiveBassBoundary R n x, (positiveBassBoundary R n x)⁻¹) :=
        connectingCoefficients_antiDiagonal R n x
      _ = (c.1, c.2) := Prod.ext hx ((congrArg Inv.inv hx).trans hc.symm)
      _ = c := rfl

/-- The original positive Bass row is exact at every displayed term, including both endpoints. -/
theorem positiveBass_fundamental (n : ℕ) :
    Function.Injective (polynomialCoefficientPair R (n + 1)) ∧
    (polynomialCoefficientPair R (n + 1)).range = (laurentDifference R (n + 1)).ker ∧
    (laurentDifference R (n + 1)).range = (positiveBassBoundary R n).ker ∧
    Function.Surjective (positiveBassBoundary R n) :=
  ⟨polynomialCoefficientPair_injective R (n + 1),
    range_coefficientPair_eq_ker_laurentDifference R n,
    range_laurentDifference_eq_ker_positiveBassBoundary R n,
    positiveBassBoundary_surjective R n⟩

/-- The same original positive row, with its trivial groups written explicitly. -/
theorem positiveBass_exactRow (n : ℕ) :
    Function.MulExact (1 : Unit →* PerfectK (Spec R) (n + 1))
      (polynomialCoefficientPair R (n + 1)) ∧
    Function.MulExact (polynomialCoefficientPair R (n + 1)) (laurentDifference R (n + 1)) ∧
    Function.MulExact (laurentDifference R (n + 1)) (positiveBassBoundary R n) ∧
    Function.MulExact (positiveBassBoundary R n) (1 : PerfectK (Spec R) n →* Unit) := by
  refine ⟨?_, MonoidHom.mulExact_iff.mpr
    (range_coefficientPair_eq_ker_laurentDifference R n).symm,
    MonoidHom.mulExact_iff.mpr (range_laurentDifference_eq_ker_positiveBassBoundary R n).symm, ?_⟩
  · intro x
    constructor
    · intro hx
      have h : x = 1 := polynomialCoefficientPair_injective R (n + 1)
        (hx.trans (map_one (polynomialCoefficientPair R (n + 1))).symm)
      exact ⟨(), h.symm⟩
    · rintro ⟨u, rfl⟩
      exact map_one (polynomialCoefficientPair R (n + 1))
  · intro x
    exact ⟨fun _ => positiveBassBoundary_surjective R n x, fun _ => rfl⟩

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
