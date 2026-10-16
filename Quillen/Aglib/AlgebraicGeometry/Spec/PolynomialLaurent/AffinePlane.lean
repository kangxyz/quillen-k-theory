/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.CoefficientSquares
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.OriginalCoordinate

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.BaseChange
public import Aglib.Algebra.Polynomial.Laurent.BaseChange

/-! # The polynomial affine plane with its original projections and section coordinates -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CommRingCat.PolynomialLaurent Quillen.PolynomialBaseChange
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
/-- The original affine-line fiber square over the base ring. -/
def polynomialSquare (R : CommRingCat.{u}) : Scheme.{u} :=
  pullback (polynomialProjection R) (polynomialProjection R)
/-- The original first polynomial projection. -/
def polynomialFirst (R : CommRingCat.{u}) : polynomialSquare R ⟶ Spec (.of (Polynomial R)) :=
  pullback.fst _ _
/-- The original second polynomial projection. -/
def polynomialSecond (R : CommRingCat.{u}) : polynomialSquare R ⟶ Spec (.of (Polynomial R)) :=
  pullback.snd _ _
/-- The actual first polynomial coordinate on the affine rectangle. -/
def rectangleFirstCoordinate (R : CommRingCat.{u}) : Γ(polynomialSquare R, ⊤) :=
  (polynomialFirst R).appTop.hom (polynomialCoordinate R)
/-- The actual second polynomial coordinate on the affine rectangle. -/
def rectangleSecondCoordinate (R : CommRingCat.{u}) : Γ(polynomialSquare R, ⊤) :=
  (polynomialSecond R).appTop.hom (polynomialCoordinate R)
/-- The actual rectangle is the spectrum of the iterated polynomial ring. -/
def polynomialSquareIso (R : CommRingCat.{u}) :
    Spec (.of (Polynomial (Polynomial R))) ≅ polynomialSquare R :=
  (polynomialProjection_isPullback (CommRingCat.ofHom (Polynomial.C (R := R)))).isoPullback
@[reassoc (attr := simp)]
theorem polynomialSquareIso_hom_first (R : CommRingCat.{u}) :
    (polynomialSquareIso R).hom ≫ polynomialFirst R =
      polynomialProjection (.of (Polynomial R)) :=
  (polynomialProjection_isPullback (CommRingCat.ofHom (Polynomial.C (R := R)))).isoPullback_hom_fst
@[reassoc (attr := simp)]
theorem polynomialSquareIso_hom_second (R : CommRingCat.{u}) :
    (polynomialSquareIso R).hom ≫ polynomialSecond R =
      Spec.map (polynomialMap (CommRingCat.ofHom (Polynomial.C (R := R)))) :=
  (polynomialProjection_isPullback (CommRingCat.ofHom (Polynomial.C (R := R)))).isoPullback_hom_snd
/-- The affine section identification induced by the actual rectangle isomorphism. -/
def rectangleSectionsIso (R : CommRingCat.{u}) :
    Γ(polynomialSquare R, ⊤) ≅ CommRingCat.of (Polynomial (Polynomial R)) :=
  Scheme.Γ.mapIso (polynomialSquareIso R).op ≪≫
    Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))
/-- The first original coordinate is the inner polynomial variable. -/
theorem rectangleSectionsIso_first (R : CommRingCat.{u}) :
    (rectangleSectionsIso R).hom.hom (rectangleFirstCoordinate R) =
      Polynomial.C Polynomial.X := by
  change (((polynomialFirst R).appTop ≫ (polynomialSquareIso R).hom.appTop ≫
    (Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))).hom).hom
      (polynomialCoordinate R)) = _
  rw [← Scheme.Hom.comp_appTop_assoc, polynomialSquareIso_hom_first]
  change (((Spec.map (CommRingCat.ofHom Polynomial.C)).appTop ≫
    (Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))).hom).hom
      (polynomialCoordinate R)) = _
  rw [Scheme.ΓSpecIso_naturality]
  simp [polynomialCoordinate]
/-- The second original coordinate is the outer polynomial variable. -/
theorem rectangleSectionsIso_second (R : CommRingCat.{u}) :
    (rectangleSectionsIso R).hom.hom (rectangleSecondCoordinate R) = Polynomial.X := by
  change (((polynomialSecond R).appTop ≫ (polynomialSquareIso R).hom.appTop ≫
    (Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))).hom).hom
      (polynomialCoordinate R)) = _
  rw [← Scheme.Hom.comp_appTop_assoc, polynomialSquareIso_hom_second]
  rw [Scheme.ΓSpecIso_naturality]
  simp [polynomialCoordinate, polynomialMap]
end AlgebraicGeometry.Scheme.ProjectiveLine
