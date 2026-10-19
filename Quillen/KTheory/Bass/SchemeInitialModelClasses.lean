/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeStageZeroComparison
public import Quillen.Waldhausen.SConstruction.Iterated.ModelStableHomotopy

/-! # Original nonnegative Model classes in the independent current-stage inclusion -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan

/-- The current class uses the original Model K/stable map and its literal initial inclusion. -/
def currentModelClass (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (x : (M.obj X).waldhausen.K n) :
    stableHomotopyGroup ((currentTelescope A).obj X) (n : ℤ) :=
  (stableHomotopyFunctor (n : ℤ)).map ((currentInitial A).app X)
    (modelKStableEquiv (M.obj X) n (Additive.ofMul x))

/-- The stable zigzag preserves this independent original Model class, including degree zero. -/
theorem currentIteratedStableIso_modelClass (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (x : (M.obj X).waldhausen.K n) :
    (currentIteratedStableIso M A X (n : ℤ)).hom (currentModelClass M A X n x) =
      (stableHomotopyFunctor (n : ℤ)).map ((iteratedInitial A).app X)
        (modelKStableEquiv (M.obj X) n (Additive.ofMul x)) :=
  ConcreteCategory.congr_hom (currentIteratedStableIso_initial M A X (n : ℤ))
    (modelKStableEquiv (M.obj X) n (Additive.ofMul x))

end Quillen.KTheory.Bass.SchemeNaturalSeed
