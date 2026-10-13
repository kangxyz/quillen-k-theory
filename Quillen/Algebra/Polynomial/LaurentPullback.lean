/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Algebra.Polynomial.LaurentCech
public import Mathlib.Algebra.Category.Ring.Constructions

/-! # The original constant pullback of Laurent chart rings

The two original maps `R[t] → R[t,t⁻¹]`, with the second coordinate inverted,
have the original coefficient ring as their categorical pullback. The lift
reads the actual constant coefficient; it is proved over arbitrary rings from
the signed degree-zero Laurent Čech kernel computation.
-/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Limits Polynomial LaurentPolynomial
open scoped LaurentPolynomial
universe u
namespace Quillen.PolynomialLaurentCech
variable (R : CommRingCat.{u})

/-- The constant-coefficient cone for the polynomial-to-Laurent pullback square. -/
def constantCone : PullbackCone
    (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R))
    (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)) :=
  PullbackCone.mk (CommRingCat.ofHom Polynomial.C) (CommRingCat.ofHom Polynomial.C) (by
    apply CommRingCat.hom_ext
    ext r
    simp)

/-- The original two polynomial-chart ring maps have the base ring as their actual pullback. -/
def constantConeIsLimit : IsLimit (constantCone R) := by
  refine PullbackCone.IsLimit.mk _
    (fun s => s.fst ≫ CommRingCat.ofHom Polynomial.constantCoeff) ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    have hw := congrArg (fun f => f x) s.condition
    change toLaurent (s.fst x) = invert (toLaurent (s.snd x)) at hw
    have hk := difference_zero_kernel R (s.fst x, s.snd x) (by
      simp only [difference_apply, T_zero, one_mul, sub_eq_zero]
      exact hw)
    have ha := congrArg Prod.fst hk
    change s.fst x = Polynomial.C ((s.snd x).coeff 0) at ha
    change Polynomial.C ((s.fst x).coeff 0) = s.fst x
    rw [ha]
    simp
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    have hw := congrArg (fun f => f x) s.condition
    change toLaurent (s.fst x) = invert (toLaurent (s.snd x)) at hw
    have hk := difference_zero_kernel R (s.fst x, s.snd x) (by
      simp only [difference_apply, T_zero, one_mul, sub_eq_zero]
      exact hw)
    have ha := congrArg Prod.fst hk
    have hb := congrArg Prod.snd hk
    change s.fst x = Polynomial.C ((s.snd x).coeff 0) at ha
    change s.snd x = Polynomial.C ((s.snd x).coeff 0) at hb
    change Polynomial.C ((s.fst x).coeff 0) = s.snd x
    rw [ha]
    simpa using hb.symm
  · intro s m hm₁ _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    have h := congrArg (fun f => Polynomial.constantCoeff (f x)) hm₁
    simpa using h

end Quillen.PolynomialLaurentCech
