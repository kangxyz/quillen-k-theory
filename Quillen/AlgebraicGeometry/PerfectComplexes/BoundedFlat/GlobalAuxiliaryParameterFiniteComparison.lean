/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientEquivalence
public import Quillen.KTheory.Bass.StrictDiagramIndexRowMapNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientSeed

/-! # Actual finite integral Spec comparisons of the three original G7 rows -/
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

/-- The actual fiber finite map retains the complete affine square and original row map. -/
def fiberFiniteComparison (i : ℕ) :=
  StrictDiagramIndexRowMap.finiteMap specUnder (laurentUnderSquareFunctor _) squareFunctor
    specSquare (F := ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)
    (G := boundedFlatCoefficientSupportedFiberModelFunctor f T ⋙ prespectrumFunctor)
    (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor) i

/-- The complete finite fiber comparison is stable on every original coefficient object. -/
theorem fiberFiniteComparison_stable
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((fiberFiniteComparison f T i).app a) := by
  change IsStableEquivalence
    (((StrictDiagramIndexChange.iterateIso specUnder (laurentUnderSquareFunctor _)
        squareFunctor specSquare i
        (ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)).hom.app a) ≫
      (((strictDiagramIterate (laurentUnderSquareFunctor _) i).map
        (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor)).app a))
  apply IsStableEquivalence.comp
  · intro d
    infer_instance
  · exact fiberComparison_iterate_stable f T _ i a

/-- The actual ambient finite map retains the complete affine square and original row map. -/
def ambientFiniteComparison (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens) (i : ℕ) :=
  StrictDiagramIndexRowMap.finiteMap specUnder (laurentUnderSquareFunctor _) squareFunctor
    specSquare (F := ParameterAuxiliarySupport.ambient T ⋙ prespectrumFunctor)
    (G := boundedFlatCoefficientSupportedAmbientModelFunctor T ⋙ prespectrumFunctor)
    (Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor) i

/-- The complete finite ambient comparison is stable on every original coefficient object. -/
theorem ambientFiniteComparison_stable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((ambientFiniteComparison Q T i).app a) := by
  change IsStableEquivalence
    (((StrictDiagramIndexChange.iterateIso specUnder (laurentUnderSquareFunctor _)
        squareFunctor specSquare i
        (ParameterAuxiliarySupport.ambient T ⋙ prespectrumFunctor)).hom.app a) ≫
      (((strictDiagramIterate (laurentUnderSquareFunctor _) i).map
        (Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor)).app a))
  apply IsStableEquivalence.comp
  · intro d
    infer_instance
  · exact ambientComparison_iterate_stable Q T _ i a

/-- The actual open finite map retains the complete affine square and original row map. -/
def openFiniteComparison (i : ℕ) :=
  StrictDiagramIndexRowMap.finiteMap specUnder (laurentUnderSquareFunctor _) squareFunctor
    specSquare (F := ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor)
    (G := boundedFlatCoefficientSupportedFullOpenModelFunctor f T ⋙ prespectrumFunctor)
    (Functor.whiskerRight (openComparison f T) prespectrumFunctor) i

omit [IsOpenImmersion f.left] in
/-- The complete finite open comparison is stable on every original coefficient object. -/
theorem openFiniteComparison_stable
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((openFiniteComparison f T i).app a) := by
  change IsStableEquivalence
    (((StrictDiagramIndexChange.iterateIso specUnder (laurentUnderSquareFunctor _)
        squareFunctor specSquare i
        (ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor)).hom.app a) ≫
      (((strictDiagramIterate (laurentUnderSquareFunctor _) i).map
        (Functor.whiskerRight (openComparison f T) prespectrumFunctor)).app a))
  apply IsStableEquivalence.comp
  · intro d
    infer_instance
  · exact openComparison_iterate_stable f T _ i a

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
