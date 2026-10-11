/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.ModelDiagramStableEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionPrespectrum
public import Quillen.KTheory.Bass.StrictRingDiagram

/-!
# Original model-diagram Bass preservation consumers

Exact original model equivalences give invertibility in negative stable degrees after every
actual Bass iterate over arbitrary index categories. Their unchanged coefficient squares and
original iterate-zero maps are retained. The actual affine section model and original Laurent
square provide an independent concrete instantiation of the generic model theorem.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.Tests.ModelDiagramBassStableEquivalence
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (F G : C ⥤ Model.{w}) (η : F ⟶ G)

/-- Actual exact-equivalence forward maps remain invertible in every negative stable degree. -/
theorem exact_model_equivalence_negative_iso (i : ℕ)
    (e : ∀ X, F.obj X ≌ G.obj X) (he : ∀ X, (e X).functor = (η.app X).functor)
    (hinv : ∀ X, IsExact (G.obj X).waldhausen.cof (G.obj X).waldhausen.weq
      (F.obj X).waldhausen.cof (F.obj X).waldhausen.weq (e X).inverse) (X : C) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (((KTheory.Bass.strictDiagramIterate Q i).map
        (Functor.whiskerRight η prespectrumFunctor)).app X)) :=
  KTheory.Bass.modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence
    Q i F G η e he hinv X _

/-- The actual transformed model arrow retains every original coefficient square. -/
theorem original_model_coefficient_square (i : ℕ) {X Y : C} (f : X ⟶ Y) :
    (((KTheory.Bass.strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).map f) ≫
        ((KTheory.Bass.strictDiagramIterate Q i).map
          (Functor.whiskerRight η prespectrumFunctor)).app Y =
      ((KTheory.Bass.strictDiagramIterate Q i).map
        (Functor.whiskerRight η prespectrumFunctor)).app X ≫
          (((KTheory.Bass.strictDiagramIterate Q i).obj (G ⋙ prespectrumFunctor)).map f) :=
  ((KTheory.Bass.strictDiagramIterate Q i).map
    (Functor.whiskerRight η prespectrumFunctor)).naturality f

/-- At iterate zero the exact original model map, rather than a chosen inverse, is retained. -/
theorem original_model_map_zero (X : C) :
    ((KTheory.Bass.strictDiagramIterate Q 0).map
      (Functor.whiskerRight η prespectrumFunctor)).app X = prespectrumMap (η.app X) := rfl

/-- Every original level value is unchanged at iterate zero, including the loop level. -/
theorem original_model_map_zero_apply (X : C) (n : ℕ)
    (x : (prespectrum (F.obj X)).space n) :
    (((KTheory.Bass.strictDiagramIterate Q 0).map
      (Functor.whiskerRight η prespectrumFunctor)).app X).map n x =
      (prespectrumMap (η.app X)).map n x := rfl

/-- The actual affine section model and original Laurent square instantiate the generic result. -/
theorem actual_section_laurent_iterate_negative_iso (i : ℕ)
    (a : PerfectComplexes.boundedFlatAffineSectionPrespectrumFunctor.{u} ⟶
      PerfectComplexes.boundedFlatAffineSectionPrespectrumFunctor)
    (ha : ∀ R, IsStableEquivalence (a.app R)) (R : CommRingCat.{u}) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (((KTheory.Bass.strictRingDiagramIterate i).map a).app R)) :=
  KTheory.Bass.modelDiagramIterate_map_isStableEquivalence
    PolynomialBaseChange.laurentSquareFunctor i
    PerfectComplexes.boundedFlatAffineSectionModelFunctor
    PerfectComplexes.boundedFlatAffineSectionModelFunctor a ha R _

end Quillen.Tests.ModelDiagramBassStableEquivalence
