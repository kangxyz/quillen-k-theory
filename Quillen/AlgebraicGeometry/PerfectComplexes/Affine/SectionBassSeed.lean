/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentHomotopy
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassDiagram
public import Quillen.Topology.Prespectrum.StrictSquareNull
public import Quillen.Topology.Prespectrum.NullLoopNaturality
public import Quillen.KTheory.Bass.StrictRingSeed

/-!
# The original strict geometric Bass seed

The original Laurent-unit track is conjugated by the actual strict-square cone null cylinder.
Both tracks are literally coefficient-natural, so this construction is an actual natural
transformation from the original section diagram to its existing Bass endofunctor value.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes

/-- The existing strict Bass square evaluated on the original section prespectrum functor. -/
def boundedFlatAffineSectionBassSquare (R : CommRingCat.{u}) :
    Arrow (Arrow LoopPrespectrum.{u+1}) :=
  boundedFlatAffineSectionPrespectrumFunctor.mapArrow.mapArrow.obj (laurentSquare R)

/-- The original coefficient map on all four corners of the actual strict Bass square. -/
def boundedFlatAffineSectionBassSquareMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionBassSquare R ⟶ boundedFlatAffineSectionBassSquare S :=
  boundedFlatAffineSectionPrespectrumFunctor.mapArrow.mapArrow.map (laurentSquareMap f)

/-- The literal mapping cone used in the existing strict Bass endofunctor. -/
def boundedFlatAffineSectionBassCone (R : CommRingCat.{u}) : LoopPrespectrum.{u+1} :=
  mappingCone (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R))

/-- The unchanged strict-square coefficient map on that actual cone. -/
def boundedFlatAffineSectionBassConeMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionBassCone R ⟶ boundedFlatAffineSectionBassCone S :=
  mappingConeMap (strictSquareComparisonFunctor.map (boundedFlatAffineSectionBassSquareMap f))

/-- The original two source legs compose to the same original Laurent coefficient inclusion. -/
theorem boundedFlatAffineSectionBassSquare_source (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassSquare R).left.hom ≫
        (boundedFlatAffineSectionBassSquare R).hom.right =
      boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R) := by
  change boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R) ≫
      boundedFlatAffineSectionPrespectrumFunctor.map (CommRingCat.ofHom Polynomial.toLaurent) = _
  rw [← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact Polynomial.toLaurent_C r

/-- The original Laurent restriction becomes null through the actual source-leg cone cylinder. -/
def boundedFlatAffineSectionBassNullHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R) ≫
      mappingConeInclusion (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R)))
      (zeroHom (boundedFlatAffineSectionPrespectrumFunctor.obj R)
        (boundedFlatAffineSectionBassCone R)) :=
  (StrictSquare.sourceNullHomotopy (boundedFlatAffineSectionBassSquare R)).cast
    (by rw [boundedFlatAffineSectionBassSquare_source]; rfl) rfl

/-- The original unit and original null cylinder define the genuine one-step strict seed. -/
def boundedFlatAffineSectionBassSeedMap (R : CommRingCat.{u}) :
    boundedFlatAffineSectionPrespectrumFunctor.obj R ⟶
      parameterLooping (boundedFlatAffineSectionBassCone R) :=
  ((boundedFlatAffineSectionLaurentUnitHomotopy R).postcomp
    (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R)))).nullLoopMap
      (boundedFlatAffineSectionBassNullHomotopy R)

/-- The original null cylinder is literally natural at every interval value. -/
theorem boundedFlatAffineSectionBassNullHomotopy_naturality_apply
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) (t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionBassConeMap f).map n
        ((boundedFlatAffineSectionBassNullHomotopy R).level n (t, x)) =
      (boundedFlatAffineSectionBassNullHomotopy S).level n
        (t, (boundedFlatAffineSectionPrespectrumFunctor.map f).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply (boundedFlatAffineSectionBassSquareMap f) n t x

/-- Conjugating those exact original tracks gives a strictly coefficient-natural seed map. -/
theorem boundedFlatAffineSectionBassSeedMap_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionBassSeedMap R ≫
        parameterLoopingMap (boundedFlatAffineSectionBassConeMap f) =
      boundedFlatAffineSectionPrespectrumFunctor.map f ≫
        boundedFlatAffineSectionBassSeedMap S := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineSectionBassSquare S))).map n
        ((boundedFlatAffineSectionPrespectrumFunctor.map (laurentMap f)).map n
          ((boundedFlatAffineSectionLaurentUnitHomotopy R).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineSectionBassSquare S))).map n
          ((boundedFlatAffineSectionLaurentUnitHomotopy S).level n
            (t, (boundedFlatAffineSectionPrespectrumFunctor.map f).map n x))
    rw [boundedFlatAffineSectionLaurentUnitHomotopy_naturality_apply]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedFlatAffineSectionBassNullHomotopy_naturality_apply f n t x

/-- The existing Bass endofunctor is the literal strict-square cone-loop composite. -/
theorem boundedFlatAffineSectionBassFunctor_eq :
    KTheory.Bass.strictRingDiagramFunctor.obj boundedFlatAffineSectionPrespectrumFunctor =
      laurentSquareFunctor ⋙ boundedFlatAffineSectionPrespectrumFunctor.mapArrow.mapArrow ⋙
        strictSquareLoopedConeFunctor := rfl

/-- The actual geometric section seed, with no supplied seed or compatibility hypothesis. -/
def boundedFlatAffineSectionBassSeed :
    boundedFlatAffineSectionPrespectrumFunctor ⟶
      KTheory.Bass.strictRingDiagramFunctor.obj boundedFlatAffineSectionPrespectrumFunctor :=
  KTheory.Bass.strictRingDiagramSeed boundedFlatAffineSectionPrespectrumFunctor
    boundedFlatAffineSectionBassSeedMap (fun f ↦ boundedFlatAffineSectionBassSeedMap_naturality f)

/-- Evaluation of the actual natural seed retains the original pointwise seed map. -/
theorem boundedFlatAffineSectionBassSeed_app (R : CommRingCat.{u}) :
    boundedFlatAffineSectionBassSeed.app R = boundedFlatAffineSectionBassSeedMap R := rfl

/-- The same original Laurent action and two original null legs remain the literal loop value. -/
theorem boundedFlatAffineSectionBassSeedMap_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) (t : unitInterval) :
    Path.toContinuousMap ((boundedFlatAffineSectionBassSeedMap R).map n x) t =
      (((boundedFlatAffineSectionLaurentUnitHomotopy R).postcomp
        (mappingConeInclusion (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R))))
        |>.conjugateToZero (boundedFlatAffineSectionBassNullHomotopy R)).level n (t, x) := rfl

end Quillen.PerfectComplexes
