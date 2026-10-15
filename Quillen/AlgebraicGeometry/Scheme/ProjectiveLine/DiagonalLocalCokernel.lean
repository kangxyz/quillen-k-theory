/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalScalarRestriction
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffinePrincipalCokernel

/-! # The original diagonal short complex in a specified affine model

Original cartesian base change and its adjunction mates identify both maps of the
restricted diagonal short complex with the literal principal-kernel presentation. Every
model hypothesis is an explicit equation of the original maps, used by the four-chart theorem.
-/
@[expose] public section
open Quillen


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})
    (j k : Spec (.of (Polynomial R)) ⟶ twoChartLine R)
    (hj : j ≫ projection R = polynomialProjection R)
    (hk : k ≫ projection R = polynomialProjection R)
    [IsOpenImmersion j] [IsOpenImmersion k]
    {S : CommRingCat.{u}} (φ : CommRingCat.of (Polynomial (Polynomial R)) ⟶ S)
    (a : Spec S ⟶ twoChartLine R) [IsOpenImmersion a]
    (hc : IsPullback a (Spec.map φ) (relativeDiagonal R) (specRectangle R j k hj hk))
/-- Original diagonal quotient target comparison for a specified actual affine cartesian model. -/
def diagonalSpecTargetIso
    (d : (Scheme.Modules.pullback (rectangleMap R j k hj hk)).obj
      ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R)) ≅
      SheafOfModules.unit (polynomialSquare R).ringCatSheaf) :
    (Scheme.Modules.restrictFunctor (specRectangle R j k hj hk)).obj
      ((Scheme.Modules.pushforward (relativeDiagonal R)).obj (tautologicalQuotientLine R)) ≅
    (Scheme.Modules.pushforward (Spec.map φ)).obj (SheafOfModules.unit (Spec S).ringCatSheaf) :=
  cartesianAdjointUnitTargetIso a (Spec.map φ) (relativeDiagonal R)
    (specRectangle R j k hj hk) hc
    ((sectionPullbackIso (relativeDiagonal R) (relativeSecond R)
      (relativeDiagonal_second R)).app (tautologicalQuotientLine R))
    (specRectangleUnitIso R j k hj hk d)
/-- The original short complex on the affine rectangle retains its literal scalar presentation. -/
def diagonalSpecSequenceIso
    (e : (Scheme.Modules.pullback (rectangleMap R j k hj hk)).obj
      ((Scheme.Modules.pullback (relativeFirst R)).obj (tautologicalLine R)) ≅
      SheafOfModules.unit (polynomialSquare R).ringCatSheaf)
    (d : (Scheme.Modules.pullback (rectangleMap R j k hj hk)).obj
      ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R)) ≅
      SheafOfModules.unit (polynomialSquare R).ringCatSheaf)
    (s : Γ(polynomialSquare R, ⊤))
    (hf : (Scheme.Modules.pullback (rectangleMap R j k hj hk)).map (diagonalIncidence R) ≫
      d.hom = e.hom ≫ unitMul (polynomialSquare R) s)
    (hs : φ.hom ((rectangleSectionsIso R).hom.hom s) = 0) :
    (diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
      (specRectangle R j k hj hk)) ≅
      affinePrincipalSequence φ ((rectangleSectionsIso R).hom.hom s) hs := by
  refine ShortComplex.isoMk (specRectangleUnitIso R j k hj hk e)
    (specRectangleUnitIso R j k hj hk d) (diagonalSpecTargetIso R j k hj hk φ a hc d) ?_ ?_
  · exact (specRectangleUnitIso_map R j k hj hk (diagonalIncidence R) e d s hf).symm
  · exact (cartesianAdjointUnitTargetIso_homEquiv a (Spec.map φ) (relativeDiagonal R)
      (specRectangle R j k hj hk) hc
      ((sectionPullbackIso (relativeDiagonal R) (relativeSecond R)
        (relativeDiagonal_second R)).app (tautologicalQuotientLine R))
      (specRectangleUnitIso R j k hj hk d)).symm
/-- The actual restricted diagonal quotient is a cokernel under its proved principal model. -/
def diagonalSpecSequenceCokernel
    (e : (Scheme.Modules.pullback (rectangleMap R j k hj hk)).obj
      ((Scheme.Modules.pullback (relativeFirst R)).obj (tautologicalLine R)) ≅
      SheafOfModules.unit (polynomialSquare R).ringCatSheaf)
    (d : (Scheme.Modules.pullback (rectangleMap R j k hj hk)).obj
      ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R)) ≅
      SheafOfModules.unit (polynomialSquare R).ringCatSheaf)
    (s : Γ(polynomialSquare R, ⊤))
    (hf : (Scheme.Modules.pullback (rectangleMap R j k hj hk)).map (diagonalIncidence R) ≫
      d.hom = e.hom ≫ unitMul (polynomialSquare R) s)
    (hs : φ.hom ((rectangleSectionsIso R).hom.hom s) = 0)
    (hker : RingHom.ker φ.hom = Ideal.span {(rectangleSectionsIso R).hom.hom s})
    (hφ : Function.Surjective φ.hom) :
    IsColimit (CokernelCofork.ofπ
      ((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
        (specRectangle R j k hj hk))).g
      ((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
        (specRectangle R j k hj hk))).zero) := by
  let E := diagonalSpecSequenceIso R j k hj hk φ a hc e d s hf hs
  have hcok := affinePrincipalSequenceCokernel φ ((rectangleSectionsIso R).hom.hom s)
    hs hker hφ
  have hExact := ShortComplex.exact_of_iso E.symm
    ((affinePrincipalSequence φ ((rectangleSectionsIso R).hom.hom s) hs).exact_of_g_is_cokernel
      hcok)
  have : Epi (affinePrincipalSequence φ ((rectangleSectionsIso R).hom.hom s) hs).g :=
    epi_of_isColimit_cofork hcok
  have : Epi (((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
      (specRectangle R j k hj hk))).g ≫ E.hom.τ₃) := by
    rw [← E.hom.comm₂₃]
    infer_instance
  have : Epi ((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
      (specRectangle R j k hj hk))).g :=
    (epi_comp_iff_of_isIso _ E.hom.τ₃).mp inferInstance
  exact hExact.gIsCokernel
end AlgebraicGeometry.Scheme.ProjectiveLine
