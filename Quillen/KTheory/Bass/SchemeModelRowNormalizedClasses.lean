/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeModelRowNormalizedPresentation
public import Quillen.KTheory.Bass.SchemeInitialModelClasses

/-!
# Original finite and nonnegative classes in the normalized-boundary presentation

The class map is defined from the actual finite zigzag comparison and the
original telescope inclusion, independently of the current telescope map.
Its comparison retains every finite stage and every nonnegative Model degree,
including zero. No new class or degree convention is used on the source.
-/
@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.KTheory.Bass.SchemeModelRowSeed
open GeometricSeedCospan NaturalTrack GeometricSquareInterchange ModelDiagramRowInterchange
variable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)) ≅ 𝟭 (M.obj (laurent.op.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).functor (unit X) (unit Y))

/-- The actual finite comparison followed by the normalized presentation's inclusion. -/
def normalizedStageInclusion (X : Scheme.{u}ᵒᵖ) (i : ℕ) :
    ModelRowZigzagSequentialization.vertex squareFunctor M X i ⟶
      normalizedPresentation M unit hunit X :=
  ZigzagSequentialization.comparison
      (ModelRowZigzagSequentialization.vertex squareFunctor M X)
      (ModelRowZigzagSequentialization.target squareFunctor M X)
      (fun j => normalizedBoundary M unit hunit j X)
      (ModelRowZigzagSequentialization.backward squareFunctor M X) i ≫
    Telescope.inclusion
      (ZigzagSequentialization.stage
        (ModelRowZigzagSequentialization.vertex squareFunctor M X)
        (ModelRowZigzagSequentialization.target squareFunctor M X)
        (fun j => normalizedBoundary M unit hunit j X)
        (ModelRowZigzagSequentialization.backward squareFunctor M X))
      (ZigzagSequentialization.transition
        (ModelRowZigzagSequentialization.vertex squareFunctor M X)
        (ModelRowZigzagSequentialization.target squareFunctor M X)
        (fun j => normalizedBoundary M unit hunit j X)
        (ModelRowZigzagSequentialization.backward squareFunctor M X)) i

/-- The original finite current inclusion has precisely the independent normalized image. -/
@[reassoc]
theorem normalizedComparison_stageInclusion (X : Scheme.{u}ᵒᵖ) (i : ℕ) :
    Telescope.inclusion (ModelRowZigzagSequentialization.vertex squareFunctor M X)
        (fun j => (SchemeNaturalSeed.currentTransition
          (ofModelUnits laurent.op coefficient M unit hunit) j).app X) i ≫
        normalizedComparison M unit hunit X =
      normalizedStageInclusion M unit hunit X i :=
  normalizedComparison_inclusion M unit hunit X i

/-- The original Model class enters through the actual normalized stage-zero inclusion. -/
def normalizedModelClass (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (M.obj X).waldhausen.K n) :
    stableHomotopyGroup (normalizedPresentation M unit hunit X) (n : ℤ) :=
  (stableHomotopyFunctor (n : ℤ)).map (normalizedStageInclusion M unit hunit X 0)
    (modelKStableEquiv (M.obj X) n (Additive.ofMul x))

/-- The actual comparison preserves each independent nonnegative class, including zero. -/
theorem normalizedComparison_modelClass (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (M.obj X).waldhausen.K n) :
    (stableHomotopyFunctor (n : ℤ)).map (normalizedComparison M unit hunit X)
      (SchemeNaturalSeed.currentModelClass M
        (ofModelUnits laurent.op coefficient M unit hunit) X n x) =
      normalizedModelClass M unit hunit X n x := by
  have hr := congrArg (stableHomotopyFunctor (n : ℤ)).map
    (normalizedComparison_stageInclusion M unit hunit X 0)
  have h := ((stableHomotopyFunctor (n : ℤ)).map_comp _ _).symm.trans hr
  exact ConcreteCategory.congr_hom h
    (modelKStableEquiv (M.obj X) n (Additive.ofMul x))

end Quillen.KTheory.Bass.SchemeModelRowSeed
