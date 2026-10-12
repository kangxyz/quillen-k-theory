/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.ModelDiagramCofiberBoundary

/-!
# Actual finite Model Bass localization-comparison consumers

Stability of the unchanged original localization cone is the input. All finite-stage point
topology and excision are proved by the production owners. These consumers keep the actual
Bass null descent, its original target inclusion, negative signed classes, and its original
single signed boundary. No seed coherence or finite-stage stabilization is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass
universe u v w
namespace Quillen.Tests.ModelDiagramCofiberPreservation
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (i j k : ℕ) (F G K : C ⥤ Model.{w})
    (a : (strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor) ⟶
      (strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor))
    (b : (strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor) ⟶
      (strictDiagramIterate Q k).obj (K ⋙ prespectrumFunctor))
    (N : ∀ X, Homotopy (a.app X ≫ b.app X)
      (zeroHom (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X)
        (((strictDiagramIterate Q k).obj (K ⋙ prespectrumFunctor)).obj X)))
    (hN : ∀ {X Y} (f : X ⟶ Y) n r x,
      ((((strictDiagramIterate Q k).obj (K ⋙ prespectrumFunctor)).map f).map n
        ((N X).level n (r, x))) =
      (N Y).level n (r, (((strictDiagramIterate Q i).obj
        (F ⋙ prespectrumFunctor)).map f).map n x))
    (hdesc : ∀ X, IsStableEquivalence (mappingConeDesc (a.app X) (b.app X) (N X)))

include hdesc in
/-- The unchanged Bass cone descent gives bijections in every signed degree. -/
theorem originalSignedDescentBijective (X : C) (d : ℤ) :
    Function.Bijective ((stableHomotopyFunctor d).map
      (mappingConeDesc (((strictDiagramFunctor Q).map a).app X)
        (((strictDiagramFunctor Q).map b).app X) (strictDiagramNullHomotopy a b N hN Q X))) := by
  let := modelDiagramCofiberDesc_bass_isStableEquivalence Q i j F G a k K b N hN hdesc X d
  exact ConcreteCategory.bijective_of_isIso _

include hdesc in
/-- Actual negative stable classes are covered without a low-level connectivity premise. -/
theorem originalNegativeDescentBijective (X : C) (d : ℕ) :
    Function.Bijective ((stableHomotopyFunctor (-((d : ℤ) + 1))).map
      (mappingConeDesc (((strictDiagramFunctor Q).map a).app X)
        (((strictDiagramFunctor Q).map b).app X) (strictDiagramNullHomotopy a b N hN Q X))) :=
  originalSignedDescentBijective Q i j k F G K a b N hN hdesc X (-((d : ℤ) + 1))

/-- The original target inclusion is carried to the unchanged Bass image of the target arrow. -/
theorem originalTargetInclusion (X : C) :
    mappingConeInclusion (((strictDiagramFunctor Q).map a).app X) ≫
        mappingConeDesc (((strictDiagramFunctor Q).map a).app X)
          (((strictDiagramFunctor Q).map b).app X) (strictDiagramNullHomotopy a b N hN Q X) =
      (((strictDiagramFunctor Q).map b).app X) :=
  mappingConeInclusion_desc _ _ _

/-- The actual quotient cylinder uses the same complete Bass null track, including level zero. -/
theorem originalZeroLevelCylinder (X : C) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj
      ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).obj X).space 0) :
    (mappingConeDesc (((strictDiagramFunctor Q).map a).app X)
      (((strictDiagramFunctor Q).map b).app X) (strictDiagramNullHomotopy a b N hN Q X)).map 0
        (ReducedMappingCone.cylinder
          ((((strictDiagramFunctor Q).obj
            ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).obj X).point 0)
          ((((strictDiagramFunctor Q).obj
            ((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor))).obj X).point 0)
          ((((strictDiagramFunctor Q).map a).app X).map 0) (r, x)) =
      (strictDiagramMapHomotopy (η := a ≫ b) (θ := diagramZeroMap _ _)
        N hN Q X).level 0 (r, x) :=
  rfl

/-- The original signed boundary and actual specified fiber lift agree on every original class. -/
theorem originalSignedBoundary (X : C) (d : ℤ)
    (x : stableHomotopyGroup (mappingCone (((strictDiagramFunctor Q).map a).app X)) (d + 1)) :
    stableFiberConnecting (((strictDiagramFunctor Q).map b).app X) d
        ((stableHomotopyFunctor (d + 1)).map
          (mappingConeDesc (((strictDiagramFunctor Q).map a).app X)
            (((strictDiagramFunctor Q).map b).app X) (strictDiagramNullHomotopy a b N hN Q X)) x) =
      (stableHomotopyFunctor d).map (homotopyFiberLift
        (((strictDiagramFunctor Q).map b).app X) (((strictDiagramFunctor Q).map a).app X)
        (strictDiagramNullHomotopy a b N hN Q X))
        (stableMappingConeConnecting (((strictDiagramFunctor Q).map a).app X)
          (modelDiagramBassMap_coneFiber_isStableEquivalence Q i j F G a X) d x) :=
  ConcreteCategory.congr_hom (modelDiagramCofiberDesc_bass_connecting Q i j F G a b N hN X d) x

end Quillen.Tests.ModelDiagramCofiberPreservation
