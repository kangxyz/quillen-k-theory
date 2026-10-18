/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictDiagramIndexChange
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseSpecSquare

/-! # The actual integral affine index square feeds the unchanged generic Bass comparison -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
universe u w
namespace QuillenTest.StrictDiagramSpecIndex

/-- The actual affine spectrum square has the exact source and target needed by Bass. -/
def bassIso (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    specUnder ⋙ (strictDiagramFunctor squareFunctor).obj F ≅
      (strictDiagramFunctor
        (laurentUnderSquareFunctor (CommRingCat.of (ULift.{u} ℤ)))).obj (specUnder ⋙ F) :=
  StrictDiagramIndexChange.iso specUnder _ squareFunctor specSquare F

/-- Its actual map uses all four original affine spectrum isomorphisms. -/
theorem bassIso_app (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (bassIso F).hom.app a = strictSquareLoopedConeFunctor.map
      (F.mapArrow.mapArrow.map (specSquareIso a).hom) := rfl

/-- The complete comparison remains natural in every spectrum diagram transformation. -/
theorem bassIso_naturality {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    Functor.whiskerLeft specUnder ((strictDiagramFunctor squareFunctor).map η) ≫
        (bassIso G).hom =
      (bassIso F).hom ≫
        (strictDiagramFunctor
          (laurentUnderSquareFunctor (CommRingCat.of (ULift.{u} ℤ)))).map
            (Functor.whiskerLeft specUnder η) :=
  StrictDiagramIndexChange.iso_naturality specUnder _ squareFunctor specSquare η

#print axioms bassIso
#print axioms bassIso_naturality

end QuillenTest.StrictDiagramSpecIndex
