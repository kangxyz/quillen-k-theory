/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassNegativeGroups
public import Mathlib.Data.ZMod.Basic

/-!
Semantic consumers for original affine Bass groups: actual ring coordinates, original K0 maps,
all-degree functor laws, Laurent representatives and kernel relations, unique descent, genuine
iterated naturality, and zero-ring/constant-group cases.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.Bass Quillen.PerfectComplexes
universe u v
namespace BassNegativeGroupsConsumers

/-- The two original coordinate inclusions retain T and its actual inverse under every ring map. -/
theorem actual_coordinate_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (laurentFunctor.map f) ((plus.app R) Polynomial.X) = LaurentPolynomial.T 1 ∧
      (laurentFunctor.map f) ((minus.app R) Polynomial.X) = LaurentPolynomial.T (-1) := by
  constructor
  · change laurentMap f.hom (Polynomial.toLaurent (Polynomial.X : Polynomial R)) = _
    rw [Polynomial.toLaurent_X,laurentMap_T]
  · change laurentMap f.hom (LaurentPolynomial.invert
      (Polynomial.toLaurent (Polynomial.X : Polynomial R))) = _
    rw [Polynomial.toLaurent_X,LaurentPolynomial.invert_T,laurentMap_T]

/-- The literal original K0 map is retained even for arbitrary nonflat ring maps. -/
theorem original_Kzero_map {R S : CommRingCat.{u}} (f : R ⟶ S)
    (a : PerfectK (Spec R) 0) :
    negativeKMap f 0 (Additive.ofMul a) = Additive.ofMul (perfectKPullback (Spec.map f) 0 a) :=
  negativeKMap_zero f a

/-- Composed maps on negative classes are the strict original recursive functor maps. -/
theorem actual_negative_composition {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (n : ℕ) (a : negativeK R (n+1)) :
    negativeKMap (f ≫ g) (n+1) a = negativeKMap g (n+1) (negativeKMap f (n+1) a) := by
  rw [negativeKMap_comp]
  rfl

/-- Changing coefficients commutes with the actual Laurent representative projection. -/
theorem actual_representative_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (a : negativeK (laurentFunctor.obj R) n) :
    negativeKπ S n (negativeKMap (laurentFunctor.map f) n a) =
      negativeKMap f (n+1) (negativeKπ R n a) :=
  congrArg (fun h ↦ h a) (negativeKπ_naturality f n)

/-- Every negative class has an original representative, with the exact two-chart zero relation. -/
theorem actual_laurent_presentation (R : CommRingCat.{u}) (n : ℕ) (y : negativeK R (n+1)) :
    ∃ x : negativeK (laurentFunctor.obj R) n, negativeKπ R n x = y ∧
      (y = 0 ↔ ∃ a b : negativeK (polynomialFunctor.obj R) n,
        negativeKMap (plus.app R) n a - negativeKMap (minus.app R) n b = x) := by
  obtain ⟨x,rfl⟩ := negativeKπ_surjective R n y
  exact ⟨x,rfl,negativeKπ_eq_zero_iff R n x⟩

/-- A prescribed map killing the two chart images has one and only one actual Bass descent. -/
theorem actual_unique_descent (R : CommRingCat.{u}) (n : ℕ) {A : AddCommGrpCat.{u+1}}
    (f : negativeK (laurentFunctor.obj R) n ⟶ A)
    (hp : negativeKMap (plus.app R) n ≫ f = 0)
    (hm : negativeKMap (minus.app R) n ≫ f = 0) :
    ∃! g : negativeK R (n+1) ⟶ A, negativeKπ R n ≫ g = f :=
  ⟨negativeKDesc R n f hp hm,negativeKπ_desc R n f hp hm,
    fun g hg ↦ negativeKDesc_unique R n f hp hm g hg⟩

/-- Functoriality in a genuine transformation preserves the entire original Laurent projection. -/
theorem actual_contraction_transformation {F G H : CommRingCat.{u} ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) (β : G ⟶ H) (R : CommRingCat.{u}) :
    (contractionπ F).app R ≫ (contractionMap α ≫ contractionMap β).app R =
      (α ≫ β).app (laurentFunctor.obj R) ≫ (contractionπ H).app R := by
  rw [← contractionMap_comp]
  exact contractionMap_π (α ≫ β) R

/-- A concrete nonzero constant group is genuinely annihilated by the Bass construction. -/
theorem constant_ZMod_six (R : CommRingCat.{u}) :
    IsZero ((contraction ((Functor.const CommRingCat.{u}).obj (AddCommGrpCat.of (ZMod 6)))).obj R)
      :=
  contraction_constant_isZero _ _

/-- No nontrivial-ring hypothesis enters the original quotient exact sequence. -/
theorem empty_spectrum_negative_sequence (n : ℕ) :
    (ShortComplex.mk (polynomialDifference (negativeKFunctor n) (CommRingCat.of (ZMod 1)))
      (negativeKπ (CommRingCat.of (ZMod 1)) n)
      (polynomialDifference_contractionπ (negativeKFunctor n) (CommRingCat.of (ZMod 1)))).Exact :=
  negativeK_exact _ n

/-- The first negative degree has the literal old flat K0 chart relation. -/
theorem original_flat_KminusOne_relation (R : CommRingCat.{u})
    (x : PerfectK (Spec (.of (LaurentPolynomial R))) 0) :
    negativeKπ R 0 (Additive.ofMul x) = 0 ↔
      ∃ a b : PerfectK (Spec (.of (Polynomial R))) 0,
        perfectKFlatPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentPlus R) 0 a *
          (perfectKFlatPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus R) 0 b)⁻¹ =
            x := by
  constructor
  · intro h
    obtain ⟨a,b,hab⟩ := (negativeKπ_eq_zero_iff R 0 (Additive.ofMul x)).mp h
    refine ⟨a.toMul,b.toMul,?_⟩
    change negativeKMap (plus.app R) 0 (Additive.ofMul a.toMul) -
      negativeKMap (minus.app R) 0 (Additive.ofMul b.toMul) = Additive.ofMul x at hab
    rw [negativeKMap_plus_zero,negativeKMap_minus_zero] at hab
    have h := congrArg (@Additive.toMul (PerfectK (Spec (.of (LaurentPolynomial R))) 0)) hab
    change _ / _ = x at h
    exact (div_eq_mul_inv _ _).symm.trans h
  · rintro ⟨a,b,hab⟩
    apply (negativeKπ_eq_zero_iff R 0 (Additive.ofMul x)).mpr
    refine ⟨Additive.ofMul a,Additive.ofMul b,?_⟩
    rw [negativeKMap_plus_zero,negativeKMap_minus_zero]
    change @Additive.ofMul (PerfectK (Spec (.of (LaurentPolynomial R))) 0)
      (perfectKFlatPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentPlus R) 0 a /
        perfectKFlatPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus R) 0 b) =
          Additive.ofMul
          x
    rw [div_eq_mul_inv,hab]

/-- Every repeated cokernel retains the prescribed transformation and original Laurent square. -/
theorem actual_iterated_transformation {F G : CommRingCat.{u} ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) (R : CommRingCat.{u}) (n : ℕ) :
    (contractionπ ((iteratedContraction n).obj F)).app R ≫
      ((iteratedContraction (n+1)).map α).app R =
    ((iteratedContraction n).map α).app (laurentFunctor.obj R) ≫
      (contractionπ ((iteratedContraction n).obj G)).app R :=
  iteratedContraction_map_π α R n

end BassNegativeGroupsConsumers

end
