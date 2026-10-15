/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.KTheory.Bass.Iteration
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.KZeroFunctor
public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialLaurent

/-!
Genuine Bass negative affine groups, starting with the unchanged original perfect K0 functor. The
public natural-number index n denotes K_{-n}; n = 0 is literally original K0. Every successor is the
actual polynomial/Laurent cokernel with its original representative map and exact two-chart
relations. Spectrum comparison, the Bass fundamental theorem, scheme globalization and negative TT
exactness are separate statements.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.Bass
open Quillen.PerfectComplexes

/-- The standard Bass recursion, starting with the unchanged original affine K0 functor. -/
def negativeKFunctor (n : ℕ) : CommRingCat.{u} ⥤ AddCommGrpCat.{u+1} :=
  (iteratedContraction n).obj affineKZeroFunctor

/-- The actual group K_{-n}(R), with K0 included at n = 0. -/
abbrev negativeK (R : CommRingCat.{u}) (n : ℕ) : AddCommGrpCat.{u+1} :=
  (negativeKFunctor n).obj R

/-- The original recursive ring-map action, with literal functor laws. -/
abbrev negativeKMap {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) :
    negativeK R n ⟶ negativeK S n := (negativeKFunctor n).map f

lemma negativeKMap_id (R : CommRingCat.{u}) (n : ℕ) :
    negativeKMap (𝟙 R) n = 𝟙 (negativeK R n) := (negativeKFunctor n).map_id R

lemma negativeKMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    negativeKMap (f ≫ g) n = negativeKMap f n ≫ negativeKMap g n :=
  (negativeKFunctor n).map_comp f g

@[simp] lemma negativeKMap_zero {R S : CommRingCat.{u}} (f : R ⟶ S)
    (a : PerfectK (Spec R) 0) :
    negativeKMap f 0 (Additive.ofMul a) = Additive.ofMul (perfectKPullback (Spec.map f) 0 a) := rfl

/-- The actual Laurent quotient map defining the next negative degree. -/
def negativeKπ (R : CommRingCat.{u}) (n : ℕ) :
    negativeK (laurentFunctor.obj R) n ⟶ negativeK R (n+1) :=
  (contractionπ (negativeKFunctor n)).app R

@[reassoc] lemma negativeKπ_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) :
    negativeKMap (laurentFunctor.map f) n ≫ negativeKπ S n =
      negativeKπ R n ≫ negativeKMap f (n+1) :=
  (contractionπ (negativeKFunctor n)).naturality f

/-- The standard Bass presentation, using the two original polynomial chart maps. -/
lemma negativeK_exact (R : CommRingCat.{u}) (n : ℕ) :
    (ShortComplex.mk (polynomialDifference (negativeKFunctor n) R) (negativeKπ R n)
      (polynomialDifference_contractionπ (negativeKFunctor n) R)).Exact :=
  contraction_exact (negativeKFunctor n) R

instance negativeKπ_epi (R : CommRingCat.{u}) (n : ℕ) : Epi (negativeKπ R n) :=
  contractionπ_epi (negativeKFunctor n) R

/-- The original additive quotient presentation of every recursively constructed Bass group. -/
def negativeKQuotientIso (R : CommRingCat.{u}) (n : ℕ) :
    negativeK R (n+1) ≅ AddCommGrpCat.of
      (negativeK (laurentFunctor.obj R) n ⧸
        AddMonoidHom.range (polynomialDifference (negativeKFunctor n) R).hom) :=
  contractionQuotientIso (negativeKFunctor n) R

@[reassoc (attr := simp)] lemma negativeKMap_plus_π (R : CommRingCat.{u}) (n : ℕ) :
    negativeKMap (plus.app R) n ≫ negativeKπ R n = 0 :=
  plus_contractionπ (negativeKFunctor n) R

@[reassoc (attr := simp)] lemma negativeKMap_minus_π (R : CommRingCat.{u}) (n : ℕ) :
    negativeKMap (minus.app R) n ≫ negativeKπ R n = 0 :=
  minus_contractionπ (negativeKFunctor n) R

/-- The initial positive chart arrow is exactly the old flat geometric K0 pullback. -/
lemma negativeKMap_plus_zero (R : CommRingCat.{u})
    (a : PerfectK (Spec (.of (Polynomial R))) 0) :
    negativeKMap (plus.app R) 0 (Additive.ofMul a) =
      Additive.ofMul (perfectKFlatPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentPlus
        R) 0 a) :=
by
  let : Flat (Spec.map (plus.app R)) :=
    AlgebraicGeometry.Scheme.PolynomialLaurent.instFlatLaurentPlus R
  exact affineKZeroFunctor_map_flat (plus.app R) a

/-- The initial inverse chart arrow is exactly the old flat geometric K0 pullback. -/
lemma negativeKMap_minus_zero (R : CommRingCat.{u})
    (a : PerfectK (Spec (.of (Polynomial R))) 0) :
    negativeKMap (minus.app R) 0 (Additive.ofMul a) =
      Additive.ofMul (perfectKFlatPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus
        R) 0 a) :=
by
  let : Flat (Spec.map (minus.app R)) :=
    AlgebraicGeometry.Scheme.PolynomialLaurent.instFlatLaurentMinus R
  exact affineKZeroFunctor_map_flat (minus.app R) a

/-- Every negative Bass class is represented by a Laurent class in the preceding degree. -/
lemma negativeKπ_surjective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Surjective (negativeKπ R n) := contractionπ_surjective (negativeKFunctor n) R

/-- The exact original two-chart relation in every negative degree. -/
lemma negativeKπ_eq_zero_iff (R : CommRingCat.{u}) (n : ℕ)
    (x : negativeK (laurentFunctor.obj R) n) :
    negativeKπ R n x = 0 ↔ ∃ a b : negativeK (polynomialFunctor.obj R) n,
      negativeKMap (plus.app R) n a - negativeKMap (minus.app R) n b = x :=
  contractionπ_eq_zero_iff (negativeKFunctor n) R x

/-- The unique descent of a Laurent homomorphism killing both original chart maps. -/
def negativeKDesc (R : CommRingCat.{u}) (n : ℕ) {A : AddCommGrpCat.{u + 1}}
    (f : negativeK (laurentFunctor.obj R) n ⟶ A)
    (hp : negativeKMap (plus.app R) n ≫ f = 0)
    (hm : negativeKMap (minus.app R) n ≫ f = 0) : negativeK R (n+1) ⟶ A :=
  contractionDescOfCharts (negativeKFunctor n) R f hp hm

@[reassoc (attr := simp)] lemma negativeKπ_desc (R : CommRingCat.{u}) (n : ℕ)
    {A : AddCommGrpCat.{u + 1}} (f : negativeK (laurentFunctor.obj R) n ⟶ A)
    (hp : negativeKMap (plus.app R) n ≫ f = 0)
    (hm : negativeKMap (minus.app R) n ≫ f = 0) :
    negativeKπ R n ≫ negativeKDesc R n f hp hm = f :=
  contractionπ_descOfCharts (negativeKFunctor n) R f hp hm

lemma negativeKDesc_unique (R : CommRingCat.{u}) (n : ℕ)
    {A : AddCommGrpCat.{u + 1}} (f : negativeK (laurentFunctor.obj R) n ⟶ A)
    (hp : negativeKMap (plus.app R) n ≫ f = 0)
    (hm : negativeKMap (minus.app R) n ≫ f = 0)
    (g : negativeK R (n + 1) ⟶ A) (hg : negativeKπ R n ≫ g = f) :
    g = negativeKDesc R n f hp hm := by
  apply contraction_hom_ext (negativeKFunctor n) R
  exact hg.trans (negativeKπ_desc R n f hp hm).symm

end Quillen.Bass

end
