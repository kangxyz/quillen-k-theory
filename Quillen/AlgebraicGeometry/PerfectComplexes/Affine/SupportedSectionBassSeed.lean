/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionDiagramLaurent
public import Quillen.Topology.Prespectrum.StrictSquareNull
public import Quillen.Topology.Prespectrum.NullLoopNaturality
public import Quillen.KTheory.Bass.StrictDiagram

/-!
# The actual Bass seed for a fixed original supported coefficient diagram

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
def boundedFlatAffineSupportedSectionBassSquare (a : Under R) :
    Arrow (Arrow LoopPrespectrum.{u+1}) :=
  (boundedFlatAffineSupportedSectionPrespectrumFunctor j).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)

/-- The original coefficient map on all four corners of the actual strict Bass square. -/
def boundedFlatAffineSupportedSectionBassSquareMap {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineSupportedSectionBassSquare j a ⟶
      boundedFlatAffineSupportedSectionBassSquare j b :=
  (boundedFlatAffineSupportedSectionPrespectrumFunctor j).mapArrow.mapArrow.map
    (laurentUnderSquareMap R f)

/-- The literal mapping cone used in the existing strict Bass endofunctor. -/
def boundedFlatAffineSupportedSectionBassCone (a : Under R) : LoopPrespectrum.{u+1} :=
  mappingCone (StrictSquare.comparison (boundedFlatAffineSupportedSectionBassSquare j a))

/-- The unchanged strict-square coefficient map on that actual cone. -/
def boundedFlatAffineSupportedSectionBassConeMap {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineSupportedSectionBassCone j a ⟶ boundedFlatAffineSupportedSectionBassCone j b :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedFlatAffineSupportedSectionBassSquareMap j f))

/-- The original two source legs compose to the same original Laurent coefficient inclusion. -/
theorem boundedFlatAffineSupportedSectionBassSquare_source (a : Under R) :
    (boundedFlatAffineSupportedSectionBassSquare j a).left.hom ≫
        (boundedFlatAffineSupportedSectionBassSquare j a).hom.right =
      (boundedFlatAffineSupportedSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a) := by
  change (boundedFlatAffineSupportedSectionPrespectrumFunctor j).map
    ((polynomialUnderCoefficient R).app a) ≫
      (boundedFlatAffineSupportedSectionPrespectrumFunctor j).map ((underToLaurent R).app a) = _
  rw [← Functor.map_comp, polynomialUnderCoefficient_toLaurent]

/-- The original Laurent restriction becomes null through the actual source-leg cone cylinder. -/
def boundedFlatAffineSupportedSectionBassNullHomotopy (a : Under R) :
    Homotopy ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).map
      ((laurentUnderCoefficient R).app a) ≫
      mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineSupportedSectionBassSquare j a)))
      (zeroHom ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a)
        (boundedFlatAffineSupportedSectionBassCone j a)) :=
  (StrictSquare.sourceNullHomotopy (boundedFlatAffineSupportedSectionBassSquare j a)).cast
    (by rw [boundedFlatAffineSupportedSectionBassSquare_source]; rfl) rfl

/-- The original unit and original null cylinder define the genuine one-step strict seed. -/
def boundedFlatAffineSupportedSectionBassSeedMap (a : Under R) :
    (boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a ⟶
      parameterLooping (boundedFlatAffineSupportedSectionBassCone j a) :=
  ((boundedFlatAffineSupportedDiagramLaurentHomotopy j a).postcomp
    (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineSupportedSectionBassSquare j a)))).nullLoopMap
      (boundedFlatAffineSupportedSectionBassNullHomotopy j a)

/-- The original null cylinder is literally natural at every interval value. -/
theorem boundedFlatAffineSupportedSectionBassNullHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineSupportedSectionBassConeMap j f).map n
        ((boundedFlatAffineSupportedSectionBassNullHomotopy j a).level n (t, x)) =
      (boundedFlatAffineSupportedSectionBassNullHomotopy j b).level n
        (t, ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).map f).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedFlatAffineSupportedSectionBassSquareMap j f) n t x

/-- Conjugating those exact original tracks gives a strictly coefficient-natural seed map. -/
theorem boundedFlatAffineSupportedSectionBassSeedMap_naturality
    {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineSupportedSectionBassSeedMap j a ≫
        parameterLoopingMap (boundedFlatAffineSupportedSectionBassConeMap j f) =
      (boundedFlatAffineSupportedSectionPrespectrumFunctor j).map f ≫
        boundedFlatAffineSupportedSectionBassSeedMap j b := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineSupportedSectionBassSquare j b))).map n
        (((boundedFlatAffineSupportedSectionPrespectrumFunctor j).map
          ((laurentUnderFunctor R).map f)).map n
          ((boundedFlatAffineSupportedDiagramLaurentHomotopy j a).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineSupportedSectionBassSquare j b))).map n
          ((boundedFlatAffineSupportedDiagramLaurentHomotopy j b).level n
            (t, ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).map f).map n x))
    rw [boundedFlatAffineSupportedDiagramLaurentHomotopy_naturality_apply j]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedFlatAffineSupportedSectionBassNullHomotopy_naturality_apply j f n t x

/-- The existing Bass endofunctor is the literal strict-square cone-loop composite. -/
theorem boundedFlatAffineSupportedSectionBassFunctor_eq :
    (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedFlatAffineSupportedSectionPrespectrumFunctor j) =
      laurentUnderSquareFunctor R ⋙
        (boundedFlatAffineSupportedSectionPrespectrumFunctor j).mapArrow.mapArrow ⋙
        strictSquareLoopedConeFunctor := rfl

/-- The actual geometric section seed, with no supplied seed or compatibility hypothesis. -/
def boundedFlatAffineSupportedSectionBassSeed :
    (boundedFlatAffineSupportedSectionPrespectrumFunctor j) ⟶
      (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedFlatAffineSupportedSectionPrespectrumFunctor j) :=
  { app := boundedFlatAffineSupportedSectionBassSeedMap j
    naturality _ _ f := (boundedFlatAffineSupportedSectionBassSeedMap_naturality j f).symm }

/-- Evaluation of the actual natural seed retains the original pointwise seed map. -/
theorem boundedFlatAffineSupportedSectionBassSeed_app (a : Under R) :
    (boundedFlatAffineSupportedSectionBassSeed j).app a =
      boundedFlatAffineSupportedSectionBassSeedMap j a := rfl

/-- The same original Laurent action and two original null legs remain the literal loop value. -/
theorem boundedFlatAffineSupportedSectionBassSeedMap_apply (a : Under R) (n : ℕ)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n)
    (t : unitInterval) :
    Path.toContinuousMap ((boundedFlatAffineSupportedSectionBassSeedMap j a).map n x) t =
      (((boundedFlatAffineSupportedDiagramLaurentHomotopy j a).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedFlatAffineSupportedSectionBassSquare j a))))
        |>.conjugateToZero
          (boundedFlatAffineSupportedSectionBassNullHomotopy j a)).level n (t, x) := rfl

end Quillen.PerfectComplexes
