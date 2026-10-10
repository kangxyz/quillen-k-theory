/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # The original two-chart Laurent Čech maps

Over any commutative ring `R`, `difference R d` is the literal signed map
`(a,b) ↦ a(t) - t^d b(t⁻¹)`. It is surjective for `d ≥ -1`, and is an actual
linear equivalence at `d = -1`. The original constant augmentation at degree
zero and the original Laurent-coefficient residue at degree minus two are
split short exact sequences, with explicit contraction identities.

These are algebraic input to projective-line cohomology. No comparison with
sheaf cohomology or preservation of perfect complexes by projective pushforward
is assumed or asserted here. All results include rings with zero divisors and
the zero ring.
-/
@[expose] public section


noncomputable section
open CategoryTheory
open Polynomial LaurentPolynomial
open scoped LaurentPolynomial
universe u
namespace Quillen.PolynomialLaurentCech
variable (R : Type u) [CommRing R]

/-- The actual signed restriction difference for the standard degree-`d` transition. -/
def difference (d : ℤ) : R[X] × R[X] →ₗ[R] R[T;T⁻¹] :=
  (Polynomial.toLaurentAlg.toLinearMap.comp (LinearMap.fst R R[X] R[X])) -
    (LinearMap.mulLeft R (T d)).comp
      ((LaurentPolynomial.invert.toLinearMap.comp Polynomial.toLaurentAlg.toLinearMap).comp
        (LinearMap.snd R R[X] R[X]))

@[simp] lemma difference_apply (d : ℤ) (a b : R[X]) :
    difference R d (a,b) = toLaurent a - T d * invert (toLaurent b) := rfl

lemma trunc_negative_part (b : R[X]) :
    trunc (T (-1) * invert (toLaurent b)) = 0 := by
  induction b using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add, mul_add, ha, hb, add_zero]
  | monomial n r =>
    simp only [Polynomial.toLaurent_C_mul_T, map_mul, invert_C, invert_T,
      T_mul, mul_T_assoc, trunc_C_mul_T]
    rw [ite_eq_right (by omega)]

lemma difference_neg_one_injective : Function.Injective (difference R (-1)) := by
  apply (difference R (-1)).ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  rintro ⟨a,b⟩ h
  have ht := congrArg trunc h
  simp only [difference_apply, map_sub, Polynomial.trunc_toLaurent,
    trunc_negative_part, sub_zero, map_zero] at ht
  have hb : toLaurent b = 0 := by
    have hmul : T (-1) * invert (toLaurent b) = 0 := by
      simpa only [difference_apply, ht, map_zero, zero_sub, neg_eq_zero] using h
    have hi : invert (toLaurent b) = 0 :=
      (isUnit_T (-1)).mul_left_cancel (by simpa using hmul)
    exact invert.injective (by simpa using hi)
  have hz : b = 0 := Polynomial.toLaurent_injective (by simpa using hb)
  exact Prod.ext ht hz

/-- The literal Čech difference is surjective in every degree at least `-1`. -/
lemma difference_surjective (d : ℤ) (hd : -1 ≤ d) :
    Function.Surjective (difference R d) := by
  intro c
  induction c using LaurentPolynomial.induction_on' with
  | add c e hc he =>
    obtain ⟨x, hx⟩ := hc
    obtain ⟨y, hy⟩ := he
    exact ⟨x + y, by rw [map_add, hx, hy]⟩
  | C_mul_T n r =>
    by_cases hn : 0 ≤ n
    · refine ⟨(Polynomial.monomial n.toNat r, 0), ?_⟩
      simp [Int.toNat_of_nonneg hn]
    · have hk : ((d - n).toNat : ℤ) = d - n := Int.toNat_of_nonneg (by omega)
      refine ⟨(0, Polynomial.monomial (d - n).toNat (-r)), ?_⟩
      simp only [difference_apply, map_zero, Polynomial.toLaurent_C_mul_T,
        map_mul, invert_C, invert_T, T_mul, mul_T_assoc, hk, map_neg,
        zero_sub, neg_mul, neg_neg]
      congr 2
      omega

/-- The original degree-minus-one Čech difference, as an actual linear isomorphism. -/
def differenceNegOneEquiv : (R[X] × R[X]) ≃ₗ[R] R[T;T⁻¹] :=
  LinearEquiv.ofBijective (difference R (-1))
    ⟨difference_neg_one_injective R, difference_surjective R (-1) le_rfl⟩

@[simp] lemma differenceNegOneEquiv_apply (a b : R[X]) :
    differenceNegOneEquiv R (a,b) = toLaurent a - T (-1) * invert (toLaurent b) := rfl

end Quillen.PolynomialLaurentCech

namespace Quillen.PolynomialLaurentCech
variable (R : Type u) [CommRing R]

/-- Multiply only the negative-chart coordinate by its polynomial variable. -/
def shiftSecond : R[X] × R[X] →ₗ[R] R[X] × R[X] :=
  (LinearMap.id : R[X] →ₗ[R] R[X]).prodMap (LinearMap.mulLeft R X)

@[simp] lemma shiftSecond_apply (a b : R[X]) : shiftSecond R (a,b) = (a,X*b) := rfl

lemma difference_shiftSecond (d : ℤ) :
    (difference R d).comp (shiftSecond R) = difference R (d-1) := by
  apply LinearMap.ext
  rintro ⟨a,b⟩
  simp only [LinearMap.comp_apply, shiftSecond_apply, difference_apply, map_mul,
    Polynomial.toLaurent_X, invert_T]
  rw [mul_left_comm (T d), ← mul_assoc, ← T_add]
  congr 3
  omega

/-- The actual constant sections on both charts. -/
def constantPair : R →ₗ[R] R[X] × R[X] :=
  (Algebra.linearMap R R[X]).prod (Algebra.linearMap R R[X])

@[simp] lemma constantPair_apply (r : R) :
    constantPair R r = (Polynomial.C r, Polynomial.C r) := rfl

/-- The coefficient-zero retraction on the negative chart. -/
def constantRetraction : R[X] × R[X] →ₗ[R] R :=
  (Polynomial.lcoeff R 0).comp (LinearMap.snd R R[X] R[X])

@[simp] lemma constantRetraction_apply (a b : R[X]) :
    constantRetraction R (a,b) = b.coeff 0 := rfl

lemma constantRetraction_constantPair :
    (constantRetraction R).comp (constantPair R) = LinearMap.id := by
  apply LinearMap.ext
  intro r
  simp

lemma difference_zero_constantPair :
    (difference R 0).comp (constantPair R) = 0 := by
  apply LinearMap.ext
  intro r
  simp

lemma trunc_invert_toLaurent (b : R[X]) :
    trunc (invert (toLaurent b)) = Polynomial.C (b.coeff 0) := by
  induction b using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add, ha, hb, Polynomial.coeff_add]
  | monomial n r =>
    cases n with
    | zero =>
      simpa using (trunc_C_mul_T (R := R) 0 r)
    | succ n =>
      simp only [Polynomial.toLaurent_C_mul_T, map_mul, invert_C, invert_T,
        trunc_C_mul_T]
      rw [ite_eq_right (by omega)]
      simp

lemma difference_zero_kernel (x : R[X] × R[X]) (hx : difference R 0 x = 0) :
    x = constantPair R (constantRetraction R x) := by
  rcases x with ⟨a,b⟩
  have h : toLaurent a = invert (toLaurent b) := by simpa using sub_eq_zero.mp hx
  have ha : a = Polynomial.C (b.coeff 0) := by
    simpa only [Polynomial.trunc_toLaurent, trunc_invert_toLaurent] using congrArg trunc h
  have hb : b = Polynomial.C (b.coeff 0) := by
    apply Polynomial.toLaurent_injective
    have hi := congrArg invert h
    simpa only [ha, Polynomial.toLaurent_C, invert_C, involutive_invert (toLaurent b)] using hi.symm
  exact Prod.ext ha hb

/-- A genuine linear section of the degree-zero signed Čech differential. -/
def zeroSection : R[T;T⁻¹] →ₗ[R] R[X] × R[X] :=
  (shiftSecond R).comp (differenceNegOneEquiv R).symm.toLinearMap

lemma difference_zeroSection :
    (difference R 0).comp (zeroSection R) = LinearMap.id := by
  unfold zeroSection
  rw [← LinearMap.comp_assoc, difference_shiftSecond]
  apply LinearMap.ext
  intro c
  exact (differenceNegOneEquiv R).apply_symm_apply c

lemma constantRetraction_zeroSection :
    (constantRetraction R).comp (zeroSection R) = 0 := by
  apply LinearMap.ext
  intro c
  change ((shiftSecond R ((differenceNegOneEquiv R).symm c)).2).coeff 0 = 0
  exact Polynomial.coeff_X_mul_zero _

/-- The exact homotopy identity for the original degree-zero two-term complex. -/
lemma zero_contraction :
    (constantPair R).comp (constantRetraction R) +
      (zeroSection R).comp (difference R 0) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hD := LinearMap.congr_fun (difference_zeroSection R) (difference R 0 x)
  have hC := LinearMap.congr_fun (constantRetraction_zeroSection R) (difference R 0 x)
  change difference R 0 (zeroSection R (difference R 0 x)) = difference R 0 x at hD
  change constantRetraction R (zeroSection R (difference R 0 x)) = 0 at hC
  have h := difference_zero_kernel R (x - zeroSection R (difference R 0 x))
    (by rw [map_sub, hD, sub_self])
  rw [map_sub, hC, sub_zero] at h
  change constantPair R (constantRetraction R x) + zeroSection R (difference R 0 x) = x
  rw [← h, sub_add_cancel]

/-- Removing the constant coefficient is linear over the original base ring. -/
def divXLinear : R[X] →ₗ[R] R[X] where
  toFun := Polynomial.divX
  map_add' _ _ := Polynomial.divX_add
  map_smul' r p := by simp [Algebra.smul_def]

/-- Remove one variable from only the second polynomial coordinate. -/
def unshiftSecond : R[X] × R[X] →ₗ[R] R[X] × R[X] :=
  (LinearMap.id : R[X] →ₗ[R] R[X]).prodMap (divXLinear R)

@[simp] lemma unshiftSecond_apply (a b : R[X]) :
    unshiftSecond R (a,b) = (a, b.divX) := rfl

lemma unshiftSecond_shiftSecond :
    (unshiftSecond R).comp (shiftSecond R) = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨a,b⟩
  change (a, (X * b).divX) = (a,b)
  apply Prod.ext
  · rfl
  · change (X * b).divX = b
    ext n
    simp

/-- The actual left inverse for the degree-minus-two differential. -/
def minusTwoRetraction : R[T;T⁻¹] →ₗ[R] R[X] × R[X] :=
  (unshiftSecond R).comp (differenceNegOneEquiv R).symm.toLinearMap

lemma minusTwoRetraction_difference :
    (minusTwoRetraction R).comp (difference R (-2)) = LinearMap.id := by
  have h := difference_shiftSecond R (-1)
  norm_num at h
  rw [← h]
  apply LinearMap.ext
  intro x
  change unshiftSecond R ((differenceNegOneEquiv R).symm
    (differenceNegOneEquiv R (shiftSecond R x))) = x
  rw [LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun (unshiftSecond_shiftSecond R) x

/-- The degree-minus-one Laurent coefficient, initially extracted via the genuine
minus-one chart isomorphism. The coefficient formula is proved separately. -/
def residue : R[T;T⁻¹] →ₗ[R] R :=
  -((constantRetraction R).comp (differenceNegOneEquiv R).symm.toLinearMap)

/-- The literal Laurent monomial of exponent minus one. -/
def residueSection : R →ₗ[R] R[T;T⁻¹] :=
  (LinearMap.mulRight R (T (-1))).comp (Algebra.linearMap R R[T;T⁻¹])

@[simp] lemma residueSection_apply (r : R) :
    residueSection R r = LaurentPolynomial.C r * T (-1) := rfl

lemma difference_neg_one_decomposition (a b : R[X]) :
    difference R (-1) (a,b) = difference R (-2) (a,b.divX) +
      residueSection R (-(b.coeff 0)) := by
  have h : (a,b) = (a, X * b.divX) + (0, Polynomial.C (b.coeff 0)) := by
    apply Prod.ext
    · simp
    · exact (Polynomial.X_mul_divX_add b).symm
  rw [h, map_add]
  have hshift := LinearMap.congr_fun (difference_shiftSecond R (-1)) (a,b.divX)
  simp only [LinearMap.comp_apply, shiftSecond_apply] at hshift
  norm_num only at hshift
  rw [hshift]
  simp only [difference_apply, residueSection_apply, map_zero, Polynomial.toLaurent_C,
    invert_C, zero_sub, map_neg]
  simp only [T_mul]

/-- The exact homotopy identity for the original degree-minus-two two-term complex. -/
lemma minusTwo_contraction :
    (difference R (-2)).comp (minusTwoRetraction R) +
      (residueSection R).comp (residue R) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  obtain ⟨⟨a,b⟩, rfl⟩ := (differenceNegOneEquiv R).surjective c
  change difference R (-2) (unshiftSecond R
      ((differenceNegOneEquiv R).symm (differenceNegOneEquiv R (a,b)))) +
    residueSection R (-(constantRetraction R
      ((differenceNegOneEquiv R).symm (differenceNegOneEquiv R (a,b))))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact (difference_neg_one_decomposition R a b).symm

lemma residue_difference_minusTwo :
    (residue R).comp (difference R (-2)) = 0 := by
  have h := difference_shiftSecond R (-1)
  norm_num at h
  rw [← h]
  apply LinearMap.ext
  intro x
  change -(constantRetraction R ((differenceNegOneEquiv R).symm
    (differenceNegOneEquiv R (shiftSecond R x)))) = 0
  rw [LinearEquiv.symm_apply_apply]
  simp only [constantRetraction, shiftSecond, LinearMap.comp_apply,
    LinearMap.snd_apply, LinearMap.prodMap_apply, LinearMap.mulLeft_apply,
    Polynomial.lcoeff_apply, Polynomial.coeff_X_mul_zero, neg_zero]

lemma residue_residueSection :
    (residue R).comp (residueSection R) = LinearMap.id := by
  apply LinearMap.ext
  intro r
  have h : residueSection R r = differenceNegOneEquiv R (0, Polynomial.C (-r)) := by
    simp [differenceNegOneEquiv_apply, T_mul]
  change residue R (residueSection R r) = r
  rw [h]
  change -(constantRetraction R ((differenceNegOneEquiv R).symm
    (differenceNegOneEquiv R (0, Polynomial.C (-r))))) = r
  rw [LinearEquiv.symm_apply_apply]
  simp

lemma coeff_toLaurent_nat (p : R[X]) (n : ℕ) :
    (toLaurent p).coeff (n : ℤ) = p.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ n

lemma coeff_toLaurent_neg (p : R[X]) (n : ℤ) (hn : n < 0) :
    (toLaurent p).coeff n = 0 := by
  apply Finsupp.notMem_support_iff.mp
  rw [support_coeff_toLaurent]
  intro h
  obtain ⟨k, _, hk⟩ := Finset.mem_map.mp h
  change (k : ℤ) = n at hk
  omega

/-- The residue is exactly the original Laurent coefficient at exponent `-1`. -/
lemma residue_eq_coeff (c : R[T;T⁻¹]) : residue R c = c.coeff (-1) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := (differenceNegOneEquiv R).surjective c
  change -(constantRetraction R ((differenceNegOneEquiv R).symm
    (differenceNegOneEquiv R (a,b)))) = _
  rw [LinearEquiv.symm_apply_apply]
  have h : T (-1) * invert (toLaurent b) = invert (toLaurent (X * b)) := by
    simp
  rw [differenceNegOneEquiv_apply, h]
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, invert_apply,
    coeff_toLaurent_neg R a (-1) (by omega), neg_neg, zero_sub,
    constantRetraction_apply]
  rw [show (1 : ℤ) = (1 : ℕ) by rfl, coeff_toLaurent_nat]
  exact congrArg Neg.neg (Polynomial.coeff_X_mul b 0).symm

end Quillen.PolynomialLaurentCech

namespace Quillen.PolynomialLaurentCech
variable (R : Type u) [CommRing R]

/-- The original constant augmentation followed by the signed degree-zero difference. -/
def zeroAugmented : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (constantPair R)) (ModuleCat.ofHom (difference R 0))
    (ModuleCat.hom_ext (difference_zero_constantPair R))

/-- The actual splitting of the degree-zero augmented sequence. -/
def zeroAugmentedSplitting : (zeroAugmented R).Splitting where
  r := ModuleCat.ofHom (constantRetraction R)
  s := ModuleCat.ofHom (zeroSection R)
  f_r := ModuleCat.hom_ext (constantRetraction_constantPair R)
  s_g := ModuleCat.hom_ext (difference_zeroSection R)
  id := ModuleCat.hom_ext (zero_contraction R)

lemma zeroAugmented_shortExact : (zeroAugmented R).ShortExact :=
  (zeroAugmentedSplitting R).shortExact

/-- The original minus-two difference followed by its actual Laurent residue. -/
def minusTwoAugmented : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (difference R (-2))) (ModuleCat.ofHom (residue R))
    (ModuleCat.hom_ext (residue_difference_minusTwo R))

/-- The genuine residue splitting, with section the monomial of exponent minus one. -/
def minusTwoAugmentedSplitting : (minusTwoAugmented R).Splitting where
  r := ModuleCat.ofHom (minusTwoRetraction R)
  s := ModuleCat.ofHom (residueSection R)
  f_r := ModuleCat.hom_ext (minusTwoRetraction_difference R)
  s_g := ModuleCat.hom_ext (residue_residueSection R)
  id := ModuleCat.hom_ext (minusTwo_contraction R)

lemma minusTwoAugmented_shortExact : (minusTwoAugmented R).ShortExact :=
  (minusTwoAugmentedSplitting R).shortExact

/-- The original degree-zero augmentation and differential survive any additive module functor. -/
def zeroAugmentedMappedSplitting {C : Type*} [Category C] [Preadditive C]
    (F : ModuleCat.{u} R ⥤ C) [F.Additive] :
    ((F.mapShortComplex).obj (zeroAugmented R)).Splitting :=
  (zeroAugmentedSplitting R).map F

end Quillen.PolynomialLaurentCech
