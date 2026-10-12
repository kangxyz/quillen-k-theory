/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.ModelDiagramCofiberComparison

/-!
# Original finite Bass cofiber comparison consumers

These clients keep the actual target inclusion, the independent cofiber and loop times,
the original coefficient cube, and signed stable classes at every actual finite Model stage.
The stability application has no supplied topology or excision hypothesis. Compatibility with
a prescribed null track or an iterated Bass seed is a separate obligation.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u v w
namespace Quillen.Tests.StrictSquareCofiberComparison
variable {S T : Arrow (Arrow LoopPrespectrum.{w})} (a : S ⟶ T)

/-- Actual target loops are carried by the original Bass image of the four cone inclusions. -/
theorem originalTargetLoop (n : ℕ)
    (γ : (strictSquareLoopedConeFunctor.obj T).space n) :
    (StrictSquare.loopedConeCofiberComparison a).map n
        ((mappingConeInclusion (strictSquareLoopedConeFunctor.map a)).map n γ) =
      (strictSquareLoopedConeFunctor.map (StrictSquare.coneSquareInclusion a)).map n γ :=
  congrArg (fun f ↦ f.map n γ) (StrictSquare.loopedConeCofiberComparison_inclusion a)

/-- The original cofiber and output-loop coordinates remain independent at level zero too. -/
theorem originalZeroLevelCylinder (r t : unitInterval)
    (γ : Path ((mappingCone (StrictSquare.comparison S)).point 0)
      ((mappingCone (StrictSquare.comparison S)).point 0)) :
    Path.toContinuousMap ((StrictSquare.loopedConeCofiberComparison a).map 0
      (ReducedMappingCone.cylinder ((strictSquareLoopedConeFunctor.obj S).point 0)
        ((strictSquareLoopedConeFunctor.obj T).point 0)
        ((strictSquareLoopedConeFunctor.map a).map 0) (r, γ))) t =
      (StrictSquare.coneInterchangeIso a).hom.map 0
        (ReducedMappingCone.cylinder ((mappingCone (StrictSquare.comparison S)).point 0)
          ((mappingCone (StrictSquare.comparison T)).point 0)
          ((mappingConeMap (strictSquareComparisonFunctor.map a)).map 0) (r, γ t)) :=
  StrictSquare.loopedConeCofiberComparison_cylinder a 0 r t γ

/-- Every actual coefficient cube commutes on original points before passing to stable classes. -/
theorem originalCoefficientCube {S' T' : Arrow (Arrow LoopPrespectrum.{w})}
    {b : S' ⟶ T'} (k : Arrow.mk a ⟶ Arrow.mk b) (n : ℕ)
    (x : (mappingCone (strictSquareLoopedConeFunctor.map a)).space n) :
    (StrictSquare.loopedConeCofiberComparison b).map n
        ((mappingConeMap (strictSquareLoopedConeFunctor.mapArrow.map k)).map n x) =
      (strictSquareLoopedConeFunctor.map (StrictSquare.coneSquareMap k)).map n
        ((StrictSquare.loopedConeCofiberComparison a).map n x) :=
  congrArg (fun f ↦ f.map n x) (StrictSquare.loopedConeCofiberComparison_naturality a k)

/-- Unchanged coefficient arrows at every actual finite stage induce all signed bijections. -/
theorem originalFiniteCoefficientBijective {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ Model.{w}) (i : ℕ)
    {X Y : C} (f : X ⟶ Y) (d : ℤ) :
    Function.Bijective ((stableHomotopyFunctor d).map
      (StrictSquare.loopedConeCofiberComparison
        ((((KTheory.Bass.strictDiagramIterate Q i).obj
          (F ⋙ prespectrumFunctor)).mapArrow.mapArrow).map (Q.map f)))) := by
  let := KTheory.Bass.modelDiagramSquare_loopedConeCofiberComparison_isStableEquivalence
    Q i F (Q.obj X) i F (Q.obj Y)
      ((((KTheory.Bass.strictDiagramIterate Q i).obj
        (F ⋙ prespectrumFunctor)).mapArrow.mapArrow).map (Q.map f)) d
  exact ConcreteCategory.bijective_of_isIso _

/-- The same original coefficient comparison includes every negative signed stable degree. -/
theorem originalNegativeCoefficientBijective {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ Model.{w}) (i k : ℕ)
    {X Y : C} (f : X ⟶ Y) :
    Function.Bijective ((stableHomotopyFunctor (-((k : ℤ) + 1))).map
      (StrictSquare.loopedConeCofiberComparison
        ((((KTheory.Bass.strictDiagramIterate Q i).obj
          (F ⋙ prespectrumFunctor)).mapArrow.mapArrow).map (Q.map f)))) :=
  originalFiniteCoefficientBijective Q F i f (-((k : ℤ) + 1))

end Quillen.Tests.StrictSquareCofiberComparison
