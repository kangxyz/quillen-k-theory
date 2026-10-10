/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassSchemeComparison

/-!
Consumers of the original geometric affine comparison and actual Bass quotient maps: arbitrary
coefficient pushouts, both coordinates and projections, chart squares, unchanged K0, all-degree maps
and representatives, unique preimages, empty spectrum and independent universes.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u v w z
namespace BassAffineSchemeComparisonConsumers
open Quillen.Bass

/-- Both coefficient extensions are actual pushouts for every original ring map. -/
theorem coefficient_pushouts {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPushout f (Quillen.PolynomialBaseChange.coefficient R)
      (Quillen.PolynomialBaseChange.coefficient S) (Quillen.PolynomialBaseChange.polynomialMap f) ∧
    IsPushout f (Quillen.PolynomialBaseChange.laurentCoefficient R)
      (Quillen.PolynomialBaseChange.laurentCoefficient S) (Quillen.PolynomialBaseChange.laurentMap
        f) :=
  ⟨Quillen.PolynomialBaseChange.polynomial_isPushout f,
    Quillen.PolynomialBaseChange.laurent_isPushout f⟩

/-- The original Laurent coordinate and its inverse survive actual coefficient extension. -/
theorem original_coordinates {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Quillen.PolynomialBaseChange.laurentMap f (LaurentPolynomial.T 1) = LaurentPolynomial.T 1 ∧
    Quillen.PolynomialBaseChange.laurentMap f (LaurentPolynomial.T (-1)) = LaurentPolynomial.T (-1)
      :=
  ⟨Quillen.PolynomialBaseChange.laurentMap_T f 1,
    Quillen.PolynomialBaseChange.laurentMap_T f (-1)⟩

/-- The actual base-product identification preserves the original structural projection. -/
theorem original_projection (R : CommRingCat.{u}) :
    (Quillen.Scheme.Bass.polynomialSpecIso R).hom ≫ pullback.fst _ _ =
      Quillen.Scheme.PolynomialLaurent.polynomialProjection R ∧
    (Quillen.Scheme.Bass.laurentSpecIso R).hom ≫ pullback.fst _ _ =
      Quillen.Scheme.PolynomialLaurent.laurentProjection R :=
  ⟨Quillen.Scheme.Bass.polynomialSpecIso_hom_fst R,
    Quillen.Scheme.Bass.laurentSpecIso_hom_fst R⟩

/-- Both chart squares use the literal natural isomorphism in the variance required by K. -/
theorem original_chart_squares (R : CommRingCat.{u}) :
    Quillen.Scheme.Bass.affineSchemeFunctor.map (plus.app R) ≫
      Quillen.Scheme.Bass.laurentDiagramIso.hom.app R =
    Quillen.Scheme.Bass.polynomialDiagramIso.hom.app R ≫
      (NatTrans.op Quillen.Scheme.Bass.plus).app (Quillen.Scheme.Bass.affineSchemeFunctor.obj R) ∧
    Quillen.Scheme.Bass.affineSchemeFunctor.map (minus.app R) ≫
      Quillen.Scheme.Bass.laurentDiagramIso.hom.app R =
    Quillen.Scheme.Bass.polynomialDiagramIso.hom.app R ≫
      (NatTrans.op Quillen.Scheme.Bass.minus).app (Quillen.Scheme.Bass.affineSchemeFunctor.obj R) :=
  ⟨Quillen.Scheme.Bass.diagramIso_plus R,Quillen.Scheme.Bass.diagramIso_minus R⟩

/-- The genuine comparison preserves every original K0 element exactly. -/
theorem original_Kzero_identity (R : CommRingCat.{u})
    (a : Quillen.PerfectComplexes.PerfectK (Spec R) 0) :
    (affineSchemeNegativeKIso 0).hom.app R (Additive.ofMul a) = Additive.ofMul a := rfl

/-- The all-degree comparison keeps arbitrary ring-map pullbacks, element by element. -/
theorem original_map_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (a : negativeK R n) :
    (affineSchemeNegativeKIso n).hom.app S (negativeKMap f n a) =
      (Quillen.PerfectComplexes.Bass.negativeKFunctor n).map
        (Quillen.Scheme.Bass.affineSchemeFunctor.map f) ((affineSchemeNegativeKIso n).hom.app R a)
          :=
  congrArg (fun g ↦ g a) (affineSchemeNegativeKIso_naturality f n)

/-- Every original Laurent representative has exactly the prescribed geometric image. -/
theorem original_representative (R : CommRingCat.{u}) (n : ℕ)
    (a : negativeK (laurentFunctor.obj R) n) :
    (affineSchemeNegativeKIso (n+1)).hom.app R (negativeKπ R n a) =
      Quillen.PerfectComplexes.Bass.negativeKπ (Quillen.Scheme.Bass.affineSchemeFunctor.obj R).unop
        n
        ((Quillen.PerfectComplexes.Bass.negativeKFunctor n).map
          (Quillen.Scheme.Bass.laurentDiagramIso.hom.app R)
            ((affineSchemeNegativeKIso n).hom.app (laurentFunctor.obj R) a)) :=
  congrArg (fun g ↦ g a) (affineSchemeNegativeKIso_π R n)

/-- Every scheme class over Spec has a unique original affine Bass class in every degree. -/
theorem original_unique_preimage (R : CommRingCat.{u}) (n : ℕ)
    (b : (Quillen.Scheme.Bass.affineSchemeFunctor ⋙
      Quillen.PerfectComplexes.Bass.negativeKFunctor n).obj R) :
    ∃! a : negativeK R n, (affineSchemeNegativeKIso n).hom.app R a = b := by
  refine ⟨(affineSchemeNegativeKIso n).inv.app R b,?_,?_⟩
  · exact congrArg (fun g ↦ g b) ((affineSchemeNegativeKIso n).inv_hom_id_app R)
  · intro a ha
    have h := congrArg (fun g ↦ g a) ((affineSchemeNegativeKIso n).hom_inv_id_app R)
    change (affineSchemeNegativeKIso n).inv.app R ((affineSchemeNegativeKIso n).hom.app R a) = a at
      h
    rw [ha] at h
    exact h.symm

/-- The empty affine scheme retains the same actual quotient square in every degree. -/
theorem empty_affine_representative (n : ℕ) :
    negativeKπ (.of (ZMod 1)) n ≫ (affineSchemeNegativeKIso (n+1)).hom.app (.of (ZMod 1)) =
      (affineSchemeNegativeKIso n).hom.app (laurentFunctor.obj (.of (ZMod 1))) ≫
        (Quillen.PerfectComplexes.Bass.negativeKFunctor n).map
          (Quillen.Scheme.Bass.laurentDiagramIso.hom.app (.of (ZMod 1))) ≫
            Quillen.PerfectComplexes.Bass.negativeKπ
              (Quillen.Scheme.Bass.affineSchemeFunctor.obj (.of (ZMod 1))).unop n :=
  affineSchemeNegativeKIso_π (.of (ZMod 1)) n

/-- Prescribed maps out of the scheme group are recovered from the original affine quotient. -/
theorem original_prescribed_descent (R : CommRingCat.{u}) (n : ℕ)
    {A : AddCommGrpCat.{u+1}}
    (g : (Quillen.Scheme.Bass.affineSchemeFunctor ⋙
      Quillen.PerfectComplexes.Bass.negativeKFunctor (n+1)).obj R ⟶ A) :
    negativeKπ R n ≫ (affineSchemeNegativeKIso (n+1)).hom.app R ≫ g =
      (affineSchemeNegativeKIso n).hom.app (laurentFunctor.obj R) ≫
        (Quillen.PerfectComplexes.Bass.negativeKFunctor n).map
          (Quillen.Scheme.Bass.laurentDiagramIso.hom.app R) ≫
            Quillen.PerfectComplexes.Bass.negativeKπ
              (Quillen.Scheme.Bass.affineSchemeFunctor.obj R).unop n ≫ g :=
  affineSchemeNegativeKIso_π_assoc R n g

/-- Cokernel transport uses independent category and group universes and the original projection. -/
theorem independent_transport {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
    {P L : C ⥤ C} {P' L' : D ⥤ D} (p m : P ⟶ L) (p' m' : P' ⟶ L')
    (T : D ⥤ C) (eP : P' ⋙ T ≅ T ⋙ P) (eL : L' ⋙ T ≅ T ⋙ L)
    (hp : ∀ X, T.map (p'.app X) ≫ eL.hom.app X = eP.hom.app X ≫ p.app (T.obj X))
    (hm : ∀ X, T.map (m'.app X) ≫ eL.hom.app X = eP.hom.app X ≫ m.app (T.obj X))
    (F : C ⥤ AddCommGrpCat.{max u z}) (X : D) :
    (TwoChart.contractionπ p' m' (T ⋙ F)).app X ≫
      (TwoChart.contractionTransportIso p m p' m' T eP eL hp hm F).hom.app X =
    F.map (eL.hom.app X) ≫ (TwoChart.contractionπ p m F).app (T.obj X) :=
  TwoChart.contractionTransportIso_π _ _ _ _ _ _ _ _ _ _ _

end BassAffineSchemeComparisonConsumers

end
