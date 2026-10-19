/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterFiniteComparison
public import Quillen.KTheory.Bass.SchemeCoefficientSeedNaturality

/-! # The original auxiliary G7 seeds under the actual complete integral Spec square -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex ParameterLaurentTrack GeometricSeedCospan

/-- The complete actual affine index square followed by a specified original row map. -/
def rowSquareComparison (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ LoopPrespectrum.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  F.mapArrow.mapArrow.map (specSquareIso a).hom ≫
    diagramSquareMap ρ (laurentUnderSquare _ a)

/-- Its source corner retains the original whole row map. -/
theorem rowSquareComparison_source (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ LoopPrespectrum.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (rowSquareComparison F G ρ a).left.left = ρ.app a := by
  change F.map (𝟙 _) ≫ ρ.app a = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Its Laurent corner is the exact original composite Model map. -/
theorem rowSquareComparison_laurent (F : Scheme.{u}ᵒᵖ ⥤ Model.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ Model.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (rowSquareComparison (F ⋙ prespectrumFunctor) (G ⋙ prespectrumFunctor)
      (Functor.whiskerRight ρ prespectrumFunctor) a).right.right =
      prespectrumMap (F.map (laurentSpecIso a.right).hom.op ≫
        ρ.app ((laurentUnderFunctor _).obj a)) := by
  change prespectrumFunctor.map _ ≫ prespectrumFunctor.map _ = _
  exact (prespectrumFunctor.map_comp _ _).symm

/-- The first Bass comparison retains the exact square cone and independent loop parameter. -/
def rowBassComparison (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ LoopPrespectrum.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) :=
  (StrictDiagramIndexChange.iso specUnder (laurentUnderSquareFunctor _)
    squareFunctor specSquare F).hom ≫ (strictDiagramFunctor (laurentUnderSquareFunctor _)).map ρ

/-- The first comparison is literally the map of the complete original square. -/
theorem rowBassComparison_app (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ LoopPrespectrum.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (rowBassComparison F G ρ).app a =
      strictSquareLoopedConeFunctor.map (rowSquareComparison F G ρ a) := by
  exact (strictSquareLoopedConeFunctor.map_comp
    (F.mapArrow.mapArrow.map (specSquareIso a).hom)
    (diagramSquareMap ρ (laurentUnderSquare _ a))).symm

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The actual ambient seed keeps the original scalar/null word through the full Spec square. -/
theorem ambient_seed_square (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens) :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (supportedTrack (T).ι)) ≫
        rowBassComparison (ParameterAuxiliarySupport.ambient T ⋙ prespectrumFunctor)
          (boundedFlatCoefficientSupportedAmbientModelFunctor T ⋙ prespectrumFunctor)
          (Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor) =
      Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor ≫
        (boundedFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).track.seed := by
  apply NatTrans.ext
  funext a
  rw [NatTrans.comp_app, NatTrans.comp_app, rowBassComparison_app]
  change (SchemeNaturalSeed.seed (supportedTrack (T).ι)).app
      (specUnder.obj a) ≫ strictSquareLoopedConeFunctor.map _ = _
  rw [SchemeCoefficientSeedNaturality.seed_naturality
    (supportedTrack (T).ι)
      (boundedFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).track
      (specUnder.obj a) a _ (by
      intro n r x
      rw [rowSquareComparison_source, rowSquareComparison_laurent]
      exact ambient_track_square Q T a n r x)]
  rw [rowSquareComparison_source]

/-- The actual fiber seed keeps the original scalar/null word through the full Spec square. -/
theorem fiber_seed_square :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (supportedTrack (T ⊔ f.left.opensRange).ι)) ≫
        rowBassComparison (ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)
          (boundedFlatCoefficientSupportedFiberModelFunctor f T ⋙ prespectrumFunctor)
          (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor) =
      Functor.whiskerRight (fiberComparison f T) prespectrumFunctor ≫
        (boundedFlatCoefficientSupportedFiberLaurentAction f T).track.seed := by
  apply NatTrans.ext
  funext a
  rw [NatTrans.comp_app, NatTrans.comp_app, rowBassComparison_app]
  change (SchemeNaturalSeed.seed (supportedTrack (T ⊔ f.left.opensRange).ι)).app
      (specUnder.obj a) ≫ strictSquareLoopedConeFunctor.map _ = _
  rw [SchemeCoefficientSeedNaturality.seed_naturality
    (supportedTrack (T ⊔ f.left.opensRange).ι)
      (boundedFlatCoefficientSupportedFiberLaurentAction f T).track
      (specUnder.obj a) a _ (by
      intro n r x
      rw [rowSquareComparison_source, rowSquareComparison_laurent]
      exact fiber_track_square f T a n r x)]
  rw [rowSquareComparison_source]

omit [IsOpenImmersion f.left] in
/-- The actual open seed keeps the original scalar/null word through the full Spec square. -/
theorem open_seed_square :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (supportedTrack (f.left ⁻¹ᵁ T).ι)) ≫
        rowBassComparison (ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor)
          (boundedFlatCoefficientSupportedFullOpenModelFunctor f T ⋙ prespectrumFunctor)
          (Functor.whiskerRight (openComparison f T) prespectrumFunctor) =
      Functor.whiskerRight (openComparison f T) prespectrumFunctor ≫
        (boundedFlatCoefficientSupportedFullOpenLaurentAction f T).track.seed := by
  apply NatTrans.ext
  funext a
  rw [NatTrans.comp_app, NatTrans.comp_app, rowBassComparison_app]
  change (SchemeNaturalSeed.seed (supportedTrack (f.left ⁻¹ᵁ T).ι)).app
      (specUnder.obj a) ≫ strictSquareLoopedConeFunctor.map _ = _
  rw [SchemeCoefficientSeedNaturality.seed_naturality
    (supportedTrack (f.left ⁻¹ᵁ T).ι)
      (boundedFlatCoefficientSupportedFullOpenLaurentAction f T).track
      (specUnder.obj a) a _ (by
      intro n r x
      rw [rowSquareComparison_source, rowSquareComparison_laurent]
      exact open_track_square f T a n r x)]
  rw [rowSquareComparison_source]

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
