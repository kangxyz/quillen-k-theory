/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionDiagramLaurent
public import Quillen.Topology.Prespectrum.StrictSquareNull
public import Quillen.Topology.Prespectrum.NullLoopNaturality
public import Quillen.KTheory.Bass.StrictDiagram

/-!
# The actual Bass seed for quotient-graded full-open sections

The original Laurent-unit track is conjugated by the actual strict-square cone null cylinder.
The same forward-T track and the original source-leg cone cylinder give a natural
transformation from the actual quotient-graded full-open section diagram to the existing Bass
endofunctor.
The polynomial square retains its positive and inverse-coordinate legs in their original order.
This construction does not assert compatibility with ambient restriction, the normalized
localization null, or any global quasi-compact quasi-separated localization theorem.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The existing strict Bass square evaluated on the original section prespectrum functor. -/
def boundedFlatAffineFullOpenGradedSectionBassSquare (a : Under R) :
    Arrow (Arrow LoopPrespectrum.{u + 1}) :=
  (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)

/-- The original coefficient map on all four corners of the actual strict Bass square. -/
def boundedFlatAffineFullOpenGradedSectionBassSquareMap {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenGradedSectionBassSquare j a ⟶
      boundedFlatAffineFullOpenGradedSectionBassSquare j b :=
  (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).mapArrow.mapArrow.map
    (laurentUnderSquareMap R f)

/-- The literal mapping cone used in the existing strict Bass endofunctor. -/
def boundedFlatAffineFullOpenGradedSectionBassCone (a : Under R) : LoopPrespectrum.{u + 1} :=
  mappingCone (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j a))

/-- The unchanged strict-square coefficient map on that actual cone. -/
def boundedFlatAffineFullOpenGradedSectionBassConeMap {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenGradedSectionBassCone j a ⟶
      boundedFlatAffineFullOpenGradedSectionBassCone j b :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedFlatAffineFullOpenGradedSectionBassSquareMap j f))

/-- The original two source legs compose to the same original Laurent coefficient inclusion. -/
theorem boundedFlatAffineFullOpenGradedSectionBassSquare_source (a : Under R) :
    (boundedFlatAffineFullOpenGradedSectionBassSquare j a).left.hom ≫
        (boundedFlatAffineFullOpenGradedSectionBassSquare j a).hom.right =
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a) := by
  change (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
    ((polynomialUnderCoefficient R).app a) ≫
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
        ((underToLaurent R).app a) = _
  rw [← Functor.map_comp, polynomialUnderCoefficient_toLaurent]

/-- The inverse-coordinate chart has the same coefficient composite, without reversing the unit. -/
theorem boundedFlatAffineFullOpenGradedSectionBassSquare_source_inverse (a : Under R) :
    (boundedFlatAffineFullOpenGradedSectionBassSquare j a).hom.left ≫
        (boundedFlatAffineFullOpenGradedSectionBassSquare j a).right.hom =
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a) := by
  change (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
    ((polynomialUnderCoefficient R).app a) ≫
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
        ((underToLaurentInvert R).app a) = _
  rw [← Functor.map_comp, polynomialUnderCoefficient_toLaurentInvert]

/-- The original Laurent restriction becomes null through the actual source-leg cone cylinder. -/
def boundedFlatAffineFullOpenGradedSectionBassNullHomotopy (a : Under R) :
    Homotopy ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
      ((laurentUnderCoefficient R).app a) ≫
      mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j a)))
      (zeroHom ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a)
        (boundedFlatAffineFullOpenGradedSectionBassCone j a)) :=
  (StrictSquare.sourceNullHomotopy (boundedFlatAffineFullOpenGradedSectionBassSquare j a)).cast
    (by rw [boundedFlatAffineFullOpenGradedSectionBassSquare_source]; rfl) rfl

/-- The original unit and original null cylinder define the genuine one-step strict seed. -/
def boundedFlatAffineFullOpenGradedSectionBassSeedMap (a : Under R) :
    (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a ⟶
      parameterLooping (boundedFlatAffineFullOpenGradedSectionBassCone j a) :=
  ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).postcomp
    (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j a)))).nullLoopMap
      (boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j a)

/-- The original null cylinder is literally natural at every interval value. -/
theorem boundedFlatAffineFullOpenGradedSectionBassNullHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineFullOpenGradedSectionBassConeMap j f).map n
        ((boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j a).level n (t, x)) =
      (boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j b).level n
        (t, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedFlatAffineFullOpenGradedSectionBassSquareMap j f) n t x

/-- Conjugating those exact original tracks gives a strictly coefficient-natural seed map. -/
theorem boundedFlatAffineFullOpenGradedSectionBassSeedMap_naturality
    {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenGradedSectionBassSeedMap j a ≫
        parameterLoopingMap (boundedFlatAffineFullOpenGradedSectionBassConeMap j f) =
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f ≫
        boundedFlatAffineFullOpenGradedSectionBassSeedMap j b := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j b))).map n
        (((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
          ((laurentUnderFunctor R).map f)).map n
          ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j b))).map n
          ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j b).level n
            (t, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x))
    rw [boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy_naturality_apply j]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedFlatAffineFullOpenGradedSectionBassNullHomotopy_naturality_apply j f n t x

/-- The existing Bass endofunctor is the literal strict-square cone-loop composite. -/
theorem boundedFlatAffineFullOpenGradedSectionBassFunctor_eq :
    (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j) =
      laurentUnderSquareFunctor R ⋙
        (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).mapArrow.mapArrow ⋙
        strictSquareLoopedConeFunctor := rfl

/-- The actual full-open section seed, with no supplied seed or compatibility hypothesis. -/
def boundedFlatAffineFullOpenGradedSectionBassSeed :
    (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j) ⟶
      (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j) :=
  { app := boundedFlatAffineFullOpenGradedSectionBassSeedMap j
    naturality _ _ f := (boundedFlatAffineFullOpenGradedSectionBassSeedMap_naturality j f).symm }

/-- Evaluation of the actual natural seed retains the original pointwise seed map. -/
theorem boundedFlatAffineFullOpenGradedSectionBassSeed_app (a : Under R) :
    (boundedFlatAffineFullOpenGradedSectionBassSeed j).app a =
      boundedFlatAffineFullOpenGradedSectionBassSeedMap j a := rfl

/-- The same original Laurent action and two original null legs remain the literal loop value. -/
theorem boundedFlatAffineFullOpenGradedSectionBassSeedMap_apply (a : Under R) (n : ℕ)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n)
    (t : unitInterval) :
    Path.toContinuousMap ((boundedFlatAffineFullOpenGradedSectionBassSeedMap j a).map n x) t =
      (((boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j a))))
        |>.conjugateToZero
          (boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j a)).level n (t, x) := rfl

end Quillen.PerfectComplexes
