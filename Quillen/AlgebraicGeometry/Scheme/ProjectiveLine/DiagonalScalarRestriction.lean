/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Scalar.TrivializationRestriction
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalAffine

/-! # Original incidence scalars on affine-spectrum rectangles

The original rectangle trivializations restrict through the actual affine model. Both
source and target maps retain the literal ΓSpec coordinates of their original global scalars.
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
/-- The actual affine-spectrum rectangle inclusion. -/
def specRectangle : Spec (.of (Polynomial (Polynomial R))) ⟶ relativeSquare R :=
  (polynomialSquareIso R).hom ≫ rectangleMap R j k hj hk
/-- The original spectrum rectangle remains an open immersion. -/
instance : IsOpenImmersion (specRectangle R j k hj hk) :=
  inferInstanceAs (IsOpenImmersion ((polynomialSquareIso R).hom ≫ rectangleMap R j k hj hk))
/-- A given original rectangle trivialization transported through the actual affine model. -/
def specRectangleUnitIso {M : (relativeSquare R).Modules}
    (e : (Scheme.Modules.pullback (rectangleMap R j k hj hk)).obj M ≅
      SheafOfModules.unit (polynomialSquare R).ringCatSheaf) :
    (Scheme.Modules.restrictFunctor (specRectangle R j k hj hk)).obj M ≅
      SheafOfModules.unit (Spec (.of (Polynomial (Polynomial R)))).ringCatSheaf :=
  (Scheme.Modules.restrictFunctorComp (polynomialSquareIso R).hom
    (rectangleMap R j k hj hk)).app M ≪≫
    restrictUnitTrivialization (polynomialSquareIso R).hom
      (restrictionUnitTrivialization (rectangleMap R j k hj hk) e)
/-- The actual affine section of a rectangle scalar retains its literal ΓSpec coordinate. -/
theorem rectangle_scalar_section (s : Γ(polynomialSquare R, ⊤)) :
    (polynomialSquareIso R).hom.appTop.hom s =
      (Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))).inv.hom
        ((rectangleSectionsIso R).hom.hom s) := by
  change (polynomialSquareIso R).hom.appTop.hom s =
    (Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))).inv
      ((Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))).hom
        ((polynomialSquareIso R).hom.appTop.hom s))
  exact (CommRingCat.inv_hom_apply _ _).symm
/-- The original rectangle scalar equation survives restriction to its actual affine model. -/
theorem specRectangleUnitIso_map {M N : (relativeSquare R).Modules} (f : M ⟶ N)
    (e : (Scheme.Modules.pullback (rectangleMap R j k hj hk)).obj M ≅
      SheafOfModules.unit (polynomialSquare R).ringCatSheaf)
    (d : (Scheme.Modules.pullback (rectangleMap R j k hj hk)).obj N ≅
      SheafOfModules.unit (polynomialSquare R).ringCatSheaf) (s : Γ(polynomialSquare R, ⊤))
    (hf : (Scheme.Modules.pullback (rectangleMap R j k hj hk)).map f ≫ d.hom =
      e.hom ≫ unitMul (polynomialSquare R) s) :
    (Scheme.Modules.restrictFunctor (specRectangle R j k hj hk)).map f ≫
      (specRectangleUnitIso R j k hj hk d).hom =
    (specRectangleUnitIso R j k hj hk e).hom ≫
      unitMul (Spec (.of (Polynomial (Polynomial R))))
        ((Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))).inv.hom
          ((rectangleSectionsIso R).hom.hom s)) := by
  have h₁ := restrictionUnitTrivialization_map (rectangleMap R j k hj hk) f e d s hf
  have h₂ := restrictUnitTrivialization_map (polynomialSquareIso R).hom
    ((Scheme.Modules.restrictFunctor (rectangleMap R j k hj hk)).map f)
    (restrictionUnitTrivialization (rectangleMap R j k hj hk) e)
    (restrictionUnitTrivialization (rectangleMap R j k hj hk) d) s h₁
  dsimp only [specRectangleUnitIso, specRectangle, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, (Scheme.Modules.restrictFunctorComp (polynomialSquareIso R).hom
    (rectangleMap R j k hj hk)).hom.naturality, Category.assoc]
  dsimp only [Functor.comp_map]
  rw [h₂, rectangle_scalar_section, Category.assoc]
end AlgebraicGeometry.Scheme.ProjectiveLine
