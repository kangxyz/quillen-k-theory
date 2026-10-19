/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterTelescopeComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientRestriction

/-!
# Actual auxiliary support squares on the original integral Spec telescopes

The original support enlargement and full restriction Model squares persist through every
finite Bass iterate. They descend literally on each original quotient cylinder to the
native supported coefficient telescope maps, retaining the fine-to-coarse restriction factor.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GeometricSeedCospan
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original actual enlargement square commutes at every finite Bass stage. -/
theorem finite_enlargement_square (i : ℕ) :
    Functor.whiskerLeft specUnder ((strictDiagramIterate squareFunctor i).map
        (ParameterAuxiliarySupport.firstMap f.left T)) ≫ ambientFiniteComparison Q T i =
      fiberFiniteComparison f T i ≫ boundedFlatCoefficientSupportedFiberBassForget f T i := by
  apply StrictDiagramIndexRowMap.finiteMap_naturality
  apply NatTrans.ext
  funext a
  have h := congrArg prespectrumFunctor.map (NatTrans.congr_app (enlargement_square f T) a)
  simpa only [NatTrans.comp_app, Functor.map_comp, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, ParameterAuxiliarySupport.firstMap,
    boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation] using h

/-- The original full restriction square retains its actual weakness-change factor at each stage. -/
theorem finite_restriction_square (i : ℕ) :
    Functor.whiskerLeft specUnder ((strictDiagramIterate squareFunctor i).map
        (ParameterAuxiliarySupport.secondMap f.left T)) ≫ openFiniteComparison f T i =
      ambientFiniteComparison Q T i ≫
        (boundedFlatCoefficientSupportedAmbientBassOpen f T i ≫
          boundedFlatCoefficientSupportedOpenBassRestriction f T i) := by
  have hrow :
      Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.secondMap f.left T) ≫
          Functor.whiskerRight (openComparison f T) prespectrumFunctor =
        Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor ≫
          (boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T ≫
            boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T) := by
    apply NatTrans.ext
    funext a
    have h := congrArg prespectrumFunctor.map (NatTrans.congr_app (restriction_square f T) a)
    simpa only [NatTrans.comp_app, Functor.map_comp, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, ParameterAuxiliarySupport.secondMap,
      boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation,
      boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation] using h
  simpa only [openFiniteComparison, ambientFiniteComparison,
    boundedFlatCoefficientSupportedAmbientBassOpen,
    boundedFlatCoefficientSupportedOpenBassRestriction, Functor.map_comp] using
    StrictDiagramIndexRowMap.finiteMap_naturality specUnder (laurentUnderSquareFunctor _)
      squareFunctor specSquare (Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor)
      (Functor.whiskerRight (openComparison f T) prespectrumFunctor)
      (ParameterAuxiliarySupport.secondMap f.left T)
      (boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T ≫
        boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T) hrow i

/-- The original support enlargement commutes with the actual complete quotient comparisons. -/
theorem telescope_enlargement_square :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.iteratedEnlargement f.left T) ≫
        ambientTelescopeComparison Q T =
      fiberTelescopeComparison f T ≫
        boundedFlatCoefficientSupportedFiberBassTelescopeForget f T := by
  apply NatTrans.ext
  funext a
  apply Telescope.hom_ext
  intro n i s x
  exact congrArg (fun y => Telescope.cylinder
    (fun j => (boundedFlatCoefficientSupportedAmbientBassDiagram T j).obj a)
    (fun j => (boundedFlatCoefficientSupportedAmbientBassTransition T j).app a) n i (s, y))
    (congrArg (fun k => k.map n x) (NatTrans.congr_app (finite_enlargement_square f T i) a))

/-- The complete quotient restriction square keeps the old native coarse-to-fine composite. -/
theorem telescope_restriction_square :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.iteratedRestriction f.left T) ≫
        openTelescopeComparison f T =
      ambientTelescopeComparison Q T ≫
        (boundedFlatCoefficientSupportedAmbientBassTelescopeOpen f T ≫
          boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T) := by
  apply NatTrans.ext
  funext a
  apply Telescope.hom_ext
  intro n i s x
  exact congrArg (fun y => Telescope.cylinder
    (fun j => (boundedFlatCoefficientSupportedFullOpenBassDiagram f T j).obj a)
    (fun j => (boundedFlatCoefficientSupportedFullOpenBassTransition f T j).app a) n i (s, y))
    (congrArg (fun k => k.map n x) (NatTrans.congr_app (finite_restriction_square f T i) a))

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
