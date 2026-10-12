/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenDiagramLaurent
public import Quillen.Topology.Prespectrum.StrictSquareNull
public import Quillen.Topology.Prespectrum.NullLoopNaturality
public import Quillen.KTheory.Bass.StrictDiagram

/-!
# The actual Bass seed for a fixed original relative-open coefficient diagram

The original Laurent-unit track is conjugated by the actual strict-square cone null cylinder.
Both tracks are proved literally natural on the fixed-open Under R diagram, so they give an
actual natural transformation to its existing Bass endofunctor. The identity-algebra level keeps
its specified pullback of j; comparison with the original j uses its separate actual projection
iso, never a literal identification of independently chosen pullback objects.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The existing strict Bass square evaluated on the original section prespectrum functor. -/
def boundedFlatAffineSectionOpenBassSquare (a : Under R) :
    Arrow (Arrow LoopPrespectrum.{u+1}) :=
  (boundedFlatAffineSectionOpenPrespectrumFunctor j).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)

/-- The original coefficient map on all four corners of the actual strict Bass square. -/
def boundedFlatAffineSectionOpenBassSquareMap {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineSectionOpenBassSquare j a ⟶
      boundedFlatAffineSectionOpenBassSquare j b :=
  (boundedFlatAffineSectionOpenPrespectrumFunctor j).mapArrow.mapArrow.map
    (laurentUnderSquareMap R f)

/-- The literal mapping cone used in the existing strict Bass endofunctor. -/
def boundedFlatAffineSectionOpenBassCone (a : Under R) : LoopPrespectrum.{u+1} :=
  mappingCone (StrictSquare.comparison (boundedFlatAffineSectionOpenBassSquare j a))

/-- The unchanged strict-square coefficient map on that actual cone. -/
def boundedFlatAffineSectionOpenBassConeMap {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineSectionOpenBassCone j a ⟶ boundedFlatAffineSectionOpenBassCone j b :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedFlatAffineSectionOpenBassSquareMap j f))

/-- The original two source legs compose to the same original Laurent coefficient inclusion. -/
theorem boundedFlatAffineSectionOpenBassSquare_source (a : Under R) :
    (boundedFlatAffineSectionOpenBassSquare j a).left.hom ≫
        (boundedFlatAffineSectionOpenBassSquare j a).hom.right =
      (boundedFlatAffineSectionOpenPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a) := by
  change (boundedFlatAffineSectionOpenPrespectrumFunctor j).map
    ((polynomialUnderCoefficient R).app a) ≫
      (boundedFlatAffineSectionOpenPrespectrumFunctor j).map ((underToLaurent R).app a) = _
  rw [← Functor.map_comp, polynomialUnderCoefficient_toLaurent]

/-- The original Laurent restriction becomes null through the actual source-leg cone cylinder. -/
def boundedFlatAffineSectionOpenBassNullHomotopy (a : Under R) :
    Homotopy ((boundedFlatAffineSectionOpenPrespectrumFunctor j).map
      ((laurentUnderCoefficient R).app a) ≫
      mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineSectionOpenBassSquare j a)))
      (zeroHom ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a)
        (boundedFlatAffineSectionOpenBassCone j a)) :=
  (StrictSquare.sourceNullHomotopy (boundedFlatAffineSectionOpenBassSquare j a)).cast
    (by rw [boundedFlatAffineSectionOpenBassSquare_source]; rfl) rfl

/-- The original unit and original null cylinder define the genuine one-step strict seed. -/
def boundedFlatAffineSectionOpenBassSeedMap (a : Under R) :
    (boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a ⟶
      parameterLooping (boundedFlatAffineSectionOpenBassCone j a) :=
  ((boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).postcomp
    (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineSectionOpenBassSquare j a)))).nullLoopMap
      (boundedFlatAffineSectionOpenBassNullHomotopy j a)

/-- The original null cylinder is literally natural at every interval value. -/
theorem boundedFlatAffineSectionOpenBassNullHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineSectionOpenBassConeMap j f).map n
        ((boundedFlatAffineSectionOpenBassNullHomotopy j a).level n (t, x)) =
      (boundedFlatAffineSectionOpenBassNullHomotopy j b).level n
        (t, ((boundedFlatAffineSectionOpenPrespectrumFunctor j).map f).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedFlatAffineSectionOpenBassSquareMap j f) n t x

/-- Conjugating those exact original tracks gives a strictly coefficient-natural seed map. -/
theorem boundedFlatAffineSectionOpenBassSeedMap_naturality
    {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineSectionOpenBassSeedMap j a ≫
        parameterLoopingMap (boundedFlatAffineSectionOpenBassConeMap j f) =
      (boundedFlatAffineSectionOpenPrespectrumFunctor j).map f ≫
        boundedFlatAffineSectionOpenBassSeedMap j b := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineSectionOpenBassSquare j b))).map n
        (((boundedFlatAffineSectionOpenPrespectrumFunctor j).map
          ((laurentUnderFunctor R).map f)).map n
          ((boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineSectionOpenBassSquare j b))).map n
          ((boundedFlatAffineSectionOpenDiagramLaurentHomotopy j b).level n
            (t, ((boundedFlatAffineSectionOpenPrespectrumFunctor j).map f).map n x))
    rw [boundedFlatAffineSectionOpenDiagramLaurentHomotopy_naturality_apply j]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedFlatAffineSectionOpenBassNullHomotopy_naturality_apply j f n t x

/-- The existing Bass endofunctor is the literal strict-square cone-loop composite. -/
theorem boundedFlatAffineSectionOpenBassFunctor_eq :
    (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedFlatAffineSectionOpenPrespectrumFunctor j) =
      laurentUnderSquareFunctor R ⋙
        (boundedFlatAffineSectionOpenPrespectrumFunctor j).mapArrow.mapArrow ⋙
        strictSquareLoopedConeFunctor := rfl

/-- The actual relative-open section seed, with no supplied seed or compatibility hypothesis. -/
def boundedFlatAffineSectionOpenBassSeed :
    (boundedFlatAffineSectionOpenPrespectrumFunctor j) ⟶
      (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedFlatAffineSectionOpenPrespectrumFunctor j) :=
  { app := boundedFlatAffineSectionOpenBassSeedMap j
    naturality _ _ f := (boundedFlatAffineSectionOpenBassSeedMap_naturality j f).symm }

/-- Evaluation of the actual natural seed retains the original pointwise seed map. -/
theorem boundedFlatAffineSectionOpenBassSeed_app (a : Under R) :
    (boundedFlatAffineSectionOpenBassSeed j).app a =
      boundedFlatAffineSectionOpenBassSeedMap j a := rfl

/-- The same original Laurent action and two original null legs remain the literal loop value. -/
theorem boundedFlatAffineSectionOpenBassSeedMap_apply (a : Under R) (n : ℕ)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n)
    (t : unitInterval) :
    Path.toContinuousMap ((boundedFlatAffineSectionOpenBassSeedMap j a).map n x) t =
      (((boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedFlatAffineSectionOpenBassSquare j a))))
        |>.conjugateToZero
          (boundedFlatAffineSectionOpenBassNullHomotopy j a)).level n (t, x) := rfl

end Quillen.PerfectComplexes
