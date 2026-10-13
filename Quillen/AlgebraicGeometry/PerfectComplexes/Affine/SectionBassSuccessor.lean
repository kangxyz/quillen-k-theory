/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassDiagram
public import Quillen.KTheory.Bass.StrictDiagramIteration

/-!
# The unchanged Bass successor as its original looped cone

The actual iteration identity identifies stage i+1 with parameter looping of the original
stage-i Laurent-square cone, as a whole strict coefficient diagram. Its equality-induced
isomorphism retains every original coefficient map and the literal loop parameter.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes

/-- The original stage-i square cones, with their unchanged strict coefficient maps. -/
def boundedFlatAffineSectionBassConeDiagram (i : ℕ) : CommRingCat.{u} ⥤ LoopPrespectrum.{u + 1} :=
  laurentSquareFunctor ⋙ (boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow ⋙
    strictSquareComparisonFunctor ⋙ mappingConeFunctor

/-- Every value is the literal original mapping cone of the actual stage-i comparison. -/
theorem boundedFlatAffineSectionBassConeDiagram_obj (i : ℕ) (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassConeDiagram i).obj R =
      mappingCone (StrictSquare.comparison
        ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare R))) := rfl

/-- Every coefficient acts through the exact original strict square cone map. -/
theorem boundedFlatAffineSectionBassConeDiagram_map (i : ℕ) {R S : CommRingCat.{u}}
    (f : R ⟶ S) :
    (boundedFlatAffineSectionBassConeDiagram i).map f =
      mappingConeMap (strictSquareComparisonFunctor.map
        ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.map (laurentSquareMap f))) := rfl

/-- The actual successor diagram equals the original stage-i cone diagram followed by looping. -/
theorem boundedFlatAffineSectionBassDiagram_succ_loopedCone (i : ℕ) :
    boundedFlatAffineSectionBassDiagram.{u} (i + 1) =
      boundedFlatAffineSectionBassConeDiagram i ⋙ parameterLoopingFunctor :=
  congrArg (fun G : (CommRingCat.{u} ⥤ LoopPrespectrum.{u + 1}) ⥤
      (CommRingCat.{u} ⥤ LoopPrespectrum.{u + 1}) =>
    G.obj boundedFlatAffineSectionPrespectrumFunctor)
      (KTheory.Bass.strictDiagramIterate_succ_right laurentSquareFunctor i)

/-- The genuine equality-induced comparison preserves the entire original coefficient diagram. -/
def boundedFlatAffineSectionBassSuccessorIso (i : ℕ) :
    boundedFlatAffineSectionBassDiagram.{u} (i + 1) ≅
      boundedFlatAffineSectionBassConeDiagram i ⋙ parameterLoopingFunctor :=
  eqToIso (boundedFlatAffineSectionBassDiagram_succ_loopedCone i)

/-- Original coefficient naturality retains the actual cone map before parameter looping. -/
theorem boundedFlatAffineSectionBassSuccessorIso_naturality (i : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffineSectionBassDiagram (i + 1)).map f ≫
        (boundedFlatAffineSectionBassSuccessorIso i).hom.app S =
      (boundedFlatAffineSectionBassSuccessorIso i).hom.app R ≫
        parameterLoopingMap (mappingConeMap (strictSquareComparisonFunctor.map
          ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.map (laurentSquareMap f)))) :=
  (boundedFlatAffineSectionBassSuccessorIso i).hom.naturality f

/-- The same original coefficient equation preserves every independent loop parameter. -/
theorem boundedFlatAffineSectionBassSuccessorIso_naturality_apply (i : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (x : ((boundedFlatAffineSectionBassDiagram (i + 1)).obj R).space n) (t : unitInterval) :
    Path.toContinuousMap
      (((boundedFlatAffineSectionBassSuccessorIso i).hom.app S).map n
        (((boundedFlatAffineSectionBassDiagram (i + 1)).map f).map n x)) t =
    (mappingConeMap (strictSquareComparisonFunctor.map
      ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.map (laurentSquareMap f)))).map n
        (Path.toContinuousMap (((boundedFlatAffineSectionBassSuccessorIso i).hom.app R).map n x)
          t) :=
  congrArg (fun k => Path.toContinuousMap (k.map n x) t)
    (boundedFlatAffineSectionBassSuccessorIso_naturality i f)

end Quillen.PerfectComplexes
