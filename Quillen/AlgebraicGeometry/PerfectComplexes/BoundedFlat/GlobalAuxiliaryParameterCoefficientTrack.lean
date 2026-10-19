/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterLaurentComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterCoefficientTrack

/-! # Whole original Laurent-action times under the auxiliary Spec comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex ParameterLaurentTrack GeometricSeedCospan

/-- Every actual Model row transformation retains the complete integral coefficient square. -/
theorem row_coefficient_square (F : Scheme.{u}ᵒᵖ ⥤ Model.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ Model.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    F.map (coefficient.app (specUnder.obj a)) ≫
        (F.map (laurentSpecIso a.right).hom.op ≫ ρ.app ((laurentUnderFunctor _).obj a)) =
      ρ.app a ≫ G.map ((laurentUnderCoefficient _).app a) := by
  have hc : coefficient.app (specUnder.obj a) ≫ (laurentSpecIso a.right).hom.op =
      specUnder.map ((laurentUnderCoefficient _).app a) := by
    apply Quiver.Hom.unop_inj
    exact laurentSpecIso_hom_fst a.right
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hc]
  exact ρ.naturality ((laurentUnderCoefficient _).app a)

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- All original scalar times and native levels are retained on the ambient row. -/
theorem ambient_track_square (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterAuxiliarySupport.ambient T).obj (specUnder.obj a))).space n) :
    (prespectrumMap (ambientLaurentMap Q T a)).map n
        (((supportedTrack (T).ι).homotopy (specUnder.obj a)).level n (r,x)) =
      (((boundedFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).track.homotopy a).level n
        (r, (prespectrumMap ((ambientComparison Q T).app a)).map n x)) := by
  have h := row_coefficient_square (ParameterAuxiliarySupport.ambient T)
    (boundedFlatCoefficientSupportedAmbientModelFunctor T) (ambientComparison Q T) a
  exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
    (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg Model.Hom.functor h))
      (supportedUnit (T).ι (specUnder.obj a))
      ((boundedFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).unit a)
      (ambientLaurentMap_unit Q T a).whisker) n r x

/-- All original scalar times and native levels are retained on the fiber row. -/
theorem fiber_track_square
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a))).space n) :
    (prespectrumMap (fiberLaurentMap f T a)).map n
        (((supportedTrack (T ⊔ f.left.opensRange).ι).homotopy (specUnder.obj a)).level n (r,x)) =
      (((boundedFlatCoefficientSupportedFiberLaurentAction f T).track.homotopy a).level n
        (r, (prespectrumMap ((fiberComparison f T).app a)).map n x)) := by
  have h := row_coefficient_square (ParameterAuxiliarySupport.fiber f.left T)
    (boundedFlatCoefficientSupportedFiberModelFunctor f T) (fiberComparison f T) a
  exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
    (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg Model.Hom.functor h))
      (supportedUnit (T ⊔ f.left.opensRange).ι (specUnder.obj a))
      ((boundedFlatCoefficientSupportedFiberLaurentAction f T).unit a)
      (fiberLaurentMap_unit f T a).whisker) n r x

omit [IsOpenImmersion f.left] in
/-- All original scalar times and native levels are retained on the open row. -/
theorem open_track_square
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterAuxiliarySupport.openModel f.left T).obj
      (specUnder.obj a))).space n) :
    (prespectrumMap (openLaurentMap f T a)).map n
        (((supportedTrack (f.left ⁻¹ᵁ T).ι).homotopy (specUnder.obj a)).level n (r,x)) =
      (((boundedFlatCoefficientSupportedFullOpenLaurentAction f T).track.homotopy a).level n
        (r, (prespectrumMap ((openComparison f T).app a)).map n x)) := by
  have h := row_coefficient_square (ParameterAuxiliarySupport.openModel f.left T)
    (boundedFlatCoefficientSupportedFullOpenModelFunctor f T) (openComparison f T) a
  exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
    (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg Model.Hom.functor h))
      (supportedUnit (f.left ⁻¹ᵁ T).ι (specUnder.obj a))
      ((boundedFlatCoefficientSupportedFullOpenLaurentAction f T).unit a)
      (openLaurentMap_unit f T a).whisker) n r x

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
