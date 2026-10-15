/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BassNegativeGroups
public import Quillen.KTheory.Bass.AffineDiagram

/-!
Original-map consumers for qc scheme Bass groups and their genuine geometric chart diagram,
including the unchanged multiplicative K0 relation and unrestricted morphism laws.
-/
@[expose] public section

open Quillen.PerfectComplexes



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
universe u v
namespace BassSchemeGroupsConsumers

/-- The relative line is the actual displayed fiber product, with no affineness premise on X. -/
theorem original_line_product (X : QuasiCompactSchemes.{u}) :
    (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.obj X).obj =
      pullback (AlgebraicGeometry.Scheme.Products.toIntegerBase X.obj)
        (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialProjection
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing) :=
          rfl

/--
Both original scheme chart maps are genuine open immersions and preserve the original projection.
-/
theorem original_chart_geometry (X : QuasiCompactSchemes.{u}) :
    IsOpenImmersion (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus.app X).hom ∧
    IsOpenImmersion (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X).hom ∧
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus.app X ≫
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialProjection.app X =
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentProjection.app X ∧
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X ≫
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialProjection.app X =
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentProjection.app X :=
  ⟨inferInstance,inferInstance,AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus_projection
    X,
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus_projection X⟩

/-- The initial original K0 map is unchanged on every actual morphism of qc schemes. -/
theorem original_Kzero_pullback {X Y : QuasiCompactSchemes.{u}} (f : X ⟶ Y)
    (a : PerfectK Y.obj 0) :
    Quillen.PerfectComplexes.Bass.negativeKPullback f 0 (Additive.ofMul a) =
      Additive.ofMul (perfectKPullback f.hom 0 a) :=
  Quillen.PerfectComplexes.Bass.negativeKPullback_zero f a

/-- Every negative degree is contravariant for all original scheme morphisms. -/
theorem original_negative_composition {X Y Z : QuasiCompactSchemes.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (a : Quillen.PerfectComplexes.Bass.negativeK Z (n+1)) :
    Quillen.PerfectComplexes.Bass.negativeKPullback (f ≫ g) (n+1) a =
      Quillen.PerfectComplexes.Bass.negativeKPullback f (n+1)
        (Quillen.PerfectComplexes.Bass.negativeKPullback g (n+1) a) := by
  rw [Quillen.PerfectComplexes.Bass.negativeKPullback_comp]
  rfl

/-- The actual Laurent representative square commutes under arbitrary scheme pullback. -/
theorem original_representative_square {X Y : QuasiCompactSchemes.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    Quillen.PerfectComplexes.Bass.negativeKPullback
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.map f) n ≫
      Quillen.PerfectComplexes.Bass.negativeKπ X n =
    Quillen.PerfectComplexes.Bass.negativeKπ Y n ≫
      Quillen.PerfectComplexes.Bass.negativeKPullback f (n+1) :=
  Quillen.PerfectComplexes.Bass.negativeKπ_naturality f n

/-- Each class has an original Laurent representative with the exact two-chart relation. -/
theorem original_laurent_presentation (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (y : Quillen.PerfectComplexes.Bass.negativeK X (n+1)) :
    ∃ x : Quillen.PerfectComplexes.Bass.negativeK
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.obj X) n,
      Quillen.PerfectComplexes.Bass.negativeKπ X n x = y ∧
      (y = 0 ↔ ∃ a b : Quillen.PerfectComplexes.Bass.negativeK
          (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.obj X) n,
        Quillen.PerfectComplexes.Bass.negativeKPullback
          (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus.app X) n a -
          Quillen.PerfectComplexes.Bass.negativeKPullback
            (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X) n b = x)
            := by
  obtain ⟨x,rfl⟩ := Quillen.PerfectComplexes.Bass.negativeKπ_surjective X n y
  exact ⟨x,rfl,Quillen.PerfectComplexes.Bass.negativeKπ_eq_zero_iff X n x⟩

/-- A prescribed Laurent map killing both actual charts has a unique original Bass descent. -/
theorem original_unique_descent (X : QuasiCompactSchemes.{u}) (n : ℕ) {A : AddCommGrpCat.{u+1}}
    (f : Quillen.PerfectComplexes.Bass.negativeK
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.obj X) n ⟶ A)
    (hp : Quillen.PerfectComplexes.Bass.negativeKPullback
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus.app X) n ≫ f =
      0)
    (hm : Quillen.PerfectComplexes.Bass.negativeKPullback
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X) n ≫ f =
      0) :
    ∃! g : Quillen.PerfectComplexes.Bass.negativeK X (n+1) ⟶ A,
      Quillen.PerfectComplexes.Bass.negativeKπ X n ≫ g = f :=
  ⟨Quillen.PerfectComplexes.Bass.negativeKDesc X n f hp hm,
    Quillen.PerfectComplexes.Bass.negativeKπ_desc X n f hp hm,
    fun g hg ↦ Quillen.PerfectComplexes.Bass.negativeKDesc_unique X n f hp hm g hg⟩

/-- The initial inverse chart map is literally the old exact flat K0 pullback. -/
theorem original_flat_chart_pullback (X : QuasiCompactSchemes.{u})
    (a : PerfectK (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.obj X).obj
      0) :
    Quillen.PerfectComplexes.Bass.negativeKPullback
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X) 0
      (Additive.ofMul a) =
      Additive.ofMul (perfectKFlatPullback
        (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X).hom 0 a) :=
  Quillen.PerfectComplexes.Bass.negativeKPullback_flat _ a

/--
General-category contraction retains the old affine projection, without universe identification.
-/
theorem original_affine_contraction_specialization
    (F : CommRingCat.{u} ⥤ AddCommGrpCat.{v}) :
    Quillen.Bass.TwoChart.contractionπ Quillen.Bass.plus Quillen.Bass.minus F =
      Quillen.Bass.contractionπ F := Quillen.Bass.twoChart_contractionπ_affine F

/-- The first negative relation retains the original multiplicative K0 law on any qc scheme. -/
theorem original_flat_KminusOne_relation (X : QuasiCompactSchemes.{u})
    (x : PerfectK (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.obj X).obj 0)
      :
    Quillen.PerfectComplexes.Bass.negativeKπ X 0 (Additive.ofMul x) = 0 ↔
      ∃ a b : PerfectK (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.obj
        X).obj 0,
        perfectKFlatPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus.app X).hom 0
          a *
          (perfectKFlatPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app
            X).hom 0 b)⁻¹ = x := by
  constructor
  · intro h
    obtain ⟨a,b,hab⟩ := (Quillen.PerfectComplexes.Bass.negativeKπ_eq_zero_iff X 0 (Additive.ofMul
      x)).mp h
    refine ⟨a.toMul,b.toMul,?_⟩
    change Quillen.PerfectComplexes.Bass.negativeKPullback
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus.app X) 0
        (Additive.ofMul a.toMul) -
      Quillen.PerfectComplexes.Bass.negativeKPullback
        (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X) 0
        (Additive.ofMul b.toMul) = Additive.ofMul x at hab
    rw [Quillen.PerfectComplexes.Bass.negativeKPullback_flat,
      Quillen.PerfectComplexes.Bass.negativeKPullback_flat] at hab
    have h := congrArg (@Additive.toMul
      (PerfectK (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.obj X).obj 0))
        hab
    change _ / _ = x at h
    exact (div_eq_mul_inv _ _).symm.trans h
  · rintro ⟨a,b,hab⟩
    apply (Quillen.PerfectComplexes.Bass.negativeKπ_eq_zero_iff X 0 (Additive.ofMul x)).mpr
    refine ⟨Additive.ofMul a,Additive.ofMul b,?_⟩
    rw [Quillen.PerfectComplexes.Bass.negativeKPullback_flat,
      Quillen.PerfectComplexes.Bass.negativeKPullback_flat]
    change @Additive.ofMul (PerfectK
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.obj X).obj 0)
      (perfectKFlatPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus.app X).hom 0 a
        /
        perfectKFlatPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X).hom 0
          b) = Additive.ofMul x
    rw [div_eq_mul_inv,hab]

/-- The actual geometric chart square is a pullback over an arbitrary original scheme. -/
theorem original_chart_pullback (X : AlgebraicGeometry.Scheme.{u}) :
    IsPullback
      ((AlgebraicGeometry.Scheme.Products.baseProductTransformation _ _
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus_projection
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)).app X)
      (pullback.snd (AlgebraicGeometry.Scheme.Products.toIntegerBase X)
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing))
      (pullback.snd (AlgebraicGeometry.Scheme.Products.toIntegerBase X)
        (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialProjection
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing))
      (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing) :=
  AlgebraicGeometry.Scheme.Products.baseProductTransformation_isPullback _ _ _ _ _

end BassSchemeGroupsConsumers

end
