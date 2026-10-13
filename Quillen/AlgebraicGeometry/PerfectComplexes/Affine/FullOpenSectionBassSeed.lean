/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionDiagramLaurent
public import Quillen.Topology.Prespectrum.StrictSquareNull
public import Quillen.Topology.Prespectrum.NullLoopNaturality
public import Quillen.KTheory.Bass.StrictDiagram

/-!
# The actual Bass seed for the original full-open section diagram

The original Laurent-unit track is conjugated by the actual strict-square cone null cylinder.
The checked forward-T track and the original source-leg cone cylinder give a natural
transformation from the actual full-open section diagram to the existing Bass endofunctor.
The polynomial square retains its positive and inverse-coordinate legs in their original order.
This construction does not assert compatibility with ambient restriction, the normalized
localization null, or any global quasi-compact quasi-separated localization theorem.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The existing strict Bass square evaluated on the original section prespectrum functor. -/
def boundedFlatAffineFullOpenSectionBassSquare (a : Under R) :
    Arrow (Arrow LoopPrespectrum.{u + 1}) :=
  (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)

/-- The original coefficient map on all four corners of the actual strict Bass square. -/
def boundedFlatAffineFullOpenSectionBassSquareMap {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenSectionBassSquare j a ⟶
      boundedFlatAffineFullOpenSectionBassSquare j b :=
  (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).mapArrow.mapArrow.map
    (laurentUnderSquareMap R f)

/-- The literal mapping cone used in the existing strict Bass endofunctor. -/
def boundedFlatAffineFullOpenSectionBassCone (a : Under R) : LoopPrespectrum.{u + 1} :=
  mappingCone (StrictSquare.comparison (boundedFlatAffineFullOpenSectionBassSquare j a))

/-- The unchanged strict-square coefficient map on that actual cone. -/
def boundedFlatAffineFullOpenSectionBassConeMap {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenSectionBassCone j a ⟶ boundedFlatAffineFullOpenSectionBassCone j b :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedFlatAffineFullOpenSectionBassSquareMap j f))

/-- The original two source legs compose to the same original Laurent coefficient inclusion. -/
theorem boundedFlatAffineFullOpenSectionBassSquare_source (a : Under R) :
    (boundedFlatAffineFullOpenSectionBassSquare j a).left.hom ≫
        (boundedFlatAffineFullOpenSectionBassSquare j a).hom.right =
      (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a) := by
  change (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
    ((polynomialUnderCoefficient R).app a) ≫
      (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map ((underToLaurent R).app a) = _
  rw [← Functor.map_comp, polynomialUnderCoefficient_toLaurent]

/-- The inverse-coordinate chart has the same coefficient composite, without reversing the unit. -/
theorem boundedFlatAffineFullOpenSectionBassSquare_source_inverse (a : Under R) :
    (boundedFlatAffineFullOpenSectionBassSquare j a).hom.left ≫
        (boundedFlatAffineFullOpenSectionBassSquare j a).right.hom =
      (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a) := by
  change (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
    ((polynomialUnderCoefficient R).app a) ≫
      (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
        ((underToLaurentInvert R).app a) = _
  rw [← Functor.map_comp, polynomialUnderCoefficient_toLaurentInvert]

/-- The original Laurent restriction becomes null through the actual source-leg cone cylinder. -/
def boundedFlatAffineFullOpenSectionBassNullHomotopy (a : Under R) :
    Homotopy ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
      ((laurentUnderCoefficient R).app a) ≫
      mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineFullOpenSectionBassSquare j a)))
      (zeroHom ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a)
        (boundedFlatAffineFullOpenSectionBassCone j a)) :=
  (StrictSquare.sourceNullHomotopy (boundedFlatAffineFullOpenSectionBassSquare j a)).cast
    (by rw [boundedFlatAffineFullOpenSectionBassSquare_source]; rfl) rfl

/-- The original unit and original null cylinder define the genuine one-step strict seed. -/
def boundedFlatAffineFullOpenSectionBassSeedMap (a : Under R) :
    (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a ⟶
      parameterLooping (boundedFlatAffineFullOpenSectionBassCone j a) :=
  ((boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).postcomp
    (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineFullOpenSectionBassSquare j a)))).nullLoopMap
      (boundedFlatAffineFullOpenSectionBassNullHomotopy j a)

/-- The original null cylinder is literally natural at every interval value. -/
theorem boundedFlatAffineFullOpenSectionBassNullHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineFullOpenSectionBassConeMap j f).map n
        ((boundedFlatAffineFullOpenSectionBassNullHomotopy j a).level n (t, x)) =
      (boundedFlatAffineFullOpenSectionBassNullHomotopy j b).level n
        (t, ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map f).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedFlatAffineFullOpenSectionBassSquareMap j f) n t x

/-- Conjugating those exact original tracks gives a strictly coefficient-natural seed map. -/
theorem boundedFlatAffineFullOpenSectionBassSeedMap_naturality
    {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenSectionBassSeedMap j a ≫
        parameterLoopingMap (boundedFlatAffineFullOpenSectionBassConeMap j f) =
      (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map f ≫
        boundedFlatAffineFullOpenSectionBassSeedMap j b := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineFullOpenSectionBassSquare j b))).map n
        (((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
          ((laurentUnderFunctor R).map f)).map n
          ((boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineFullOpenSectionBassSquare j b))).map n
          ((boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j b).level n
            (t, ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map f).map n x))
    rw [boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy_naturality_apply j]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedFlatAffineFullOpenSectionBassNullHomotopy_naturality_apply j f n t x

/-- The existing Bass endofunctor is the literal strict-square cone-loop composite. -/
theorem boundedFlatAffineFullOpenSectionBassFunctor_eq :
    (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedFlatAffineFullOpenSectionPrespectrumFunctor j) =
      laurentUnderSquareFunctor R ⋙
        (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).mapArrow.mapArrow ⋙
        strictSquareLoopedConeFunctor := rfl

/-- The actual full-open section seed, with no supplied seed or compatibility hypothesis. -/
def boundedFlatAffineFullOpenSectionBassSeed :
    (boundedFlatAffineFullOpenSectionPrespectrumFunctor j) ⟶
      (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedFlatAffineFullOpenSectionPrespectrumFunctor j) :=
  { app := boundedFlatAffineFullOpenSectionBassSeedMap j
    naturality _ _ f := (boundedFlatAffineFullOpenSectionBassSeedMap_naturality j f).symm }

/-- Evaluation of the actual natural seed retains the original pointwise seed map. -/
theorem boundedFlatAffineFullOpenSectionBassSeed_app (a : Under R) :
    (boundedFlatAffineFullOpenSectionBassSeed j).app a =
      boundedFlatAffineFullOpenSectionBassSeedMap j a := rfl

/-- The same original Laurent action and two original null legs remain the literal loop value. -/
theorem boundedFlatAffineFullOpenSectionBassSeedMap_apply (a : Under R) (n : ℕ)
    (x : ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a).space n)
    (t : unitInterval) :
    Path.toContinuousMap ((boundedFlatAffineFullOpenSectionBassSeedMap j a).map n x) t =
      (((boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedFlatAffineFullOpenSectionBassSquare j a))))
        |>.conjugateToZero
          (boundedFlatAffineFullOpenSectionBassNullHomotopy j a)).level n (t, x) := rfl

end Quillen.PerfectComplexes
