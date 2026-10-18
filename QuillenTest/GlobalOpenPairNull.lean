/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenPairNull

/-! # The actual parameter null retains the complete original reversed transformation -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterModels
universe u
namespace QuillenTest.GlobalOpenPairNull

/-- Original null time is reversed exactly once, at every genuine parameter and spectrum level. -/
example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((supported f).obj X)).space n) :
    ((supportedOpenNull f).homotopy X).level n (s, x) =
      (prespectrumTransformationHomotopy (zeroToOpen f X) (zeroToOpen_weak f X)).level n
        (unitInterval.symm s, x) :=
  prespectrumCompositeZeroNullHomotopy_level
    ((forget f).app X) ((changeWeak f).app X) (zeroToOpen f X) (zeroToOpen_weak f X) n s x

end QuillenTest.GlobalOpenPairNull
