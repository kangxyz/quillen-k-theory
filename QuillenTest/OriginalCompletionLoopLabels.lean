/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.KTheory.Plus.ProjectiveCompletionLoopLabels
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-! # Actual completion-loop labels, original stages, and arbitrary rings -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
universe u
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal

-- Every displayed basepoint is neutral, including those of nonzero old algebraic grade.
example {R : Type u} [Ring R] (U : GroupCompletionCategory R) :
    (exactStructure R).loopComponentsKZeroEquiv
      (ZerothHomotopy.mk (completionToOriginalQLoops R U (classifyingSpacePoint U))) = 1 := by
  rw [← completionToOriginalQLoopsComponents_mk, completionToOriginalQLoopsComponents_kZero,
    completionZerothHomotopyKZeroEquiv_point, div_self']

-- Every diagonal telescope stage has neutral original Q-loop label without a rank hypothesis.
example {R : Type u} [Ring R] (n : ℕ) :
    (exactStructure Rᵐᵒᵖ).loopComponentsKZeroEquiv
      (ZerothHomotopy.mk (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0)
        (classifyingSpacePoint
          (completionPair Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) (rankOnePower Rᵐᵒᵖ n))))) = 1 := by
  rw [completionToOriginalQLoops_stage_kZero, div_self']

-- Ring change to the zero ring retains the exact original K-map and the actual loop label.
example (a : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory ℤᵐᵒᵖ))) :
    (rightBaseChangeExact (Int.castRingHom (ZMod 1))).KMap 0
      ((exactStructure ℤᵐᵒᵖ).loopComponentsKZeroEquiv
        (completionToOriginalQLoopsComponents ℤᵐᵒᵖ (StableCompletion.stageObject ℤ 0) a)) =
      (exactStructure (ZMod 1)ᵐᵒᵖ).loopComponentsKZeroEquiv
        (completionToOriginalQLoopsComponents (ZMod 1)ᵐᵒᵖ
          (StableCompletion.stageObject (ZMod 1) 0)
          (completionZerothHomotopyBaseChange (Int.castRingHom (ZMod 1)) a)) :=
  completionToOriginalQLoopsComponents_kZero_baseChange (Int.castRingHom (ZMod 1)) a

-- Over a noncommutative matrix ring the original algebraic retraction verifies the exact sign.
example (n : ℕ) (P : IsoCategory (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ) :
    (exactStructure (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ).kZeroToGrothendieck
      ((exactStructure (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ).loopComponentsKZeroEquiv
        (ZerothHomotopy.mk
          (completionToOriginalQLoops (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ
            (StableCompletion.stageObject (Matrix (Fin 2) (Fin 2) ℤ) 0)
            (classifyingSpacePoint (completionPair (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ
              (rankOnePower (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ n) P))))) =
      Multiplicative.ofAdd
        ((exactStructure (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ).grothendieckClass P.of -
          (exactStructure (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ).grothendieckClass
            (rankOnePower (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ n).of) := by
  rw [completionToOriginalQLoops_stage_kZero, map_div,
    ExactStructure.kZeroToGrothendieck_objectClass,
    ExactStructure.kZeroToGrothendieck_objectClass, ofAdd_sub]

-- A nonzero displayed grade still subtracts that exact basepoint class.
example {R : Type u} [Ring R] (U : GroupCompletionCategory R)
    (_hU : completionGrade R U ≠ 0)
    (a : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory R))) :
    (exactStructure R).loopComponentsKZeroEquiv (completionToOriginalQLoopsComponents R U a) =
      completionZerothHomotopyKZeroEquiv R a / completionKZeroClass R U :=
  completionToOriginalQLoopsComponents_kZero R U a

-- The actual additive-zero-pair comparison, without a supplied zero-grade premise.
example {R : Type u} [Ring R] (A B : IsoCategory R) :
    (exactStructure R).loopComponentsKZeroEquiv
      (ZerothHomotopy.mk (originalQComparison R
        (classifyingSpacePoint (completionPair R A B)))) =
      (exactStructure R).kZeroObjectClass B.of / (exactStructure R).kZeroObjectClass A.of := by
  rw [originalQComparison_kZero, completionZerothHomotopyKZeroEquiv_pair]

-- Every positive stage retains its actual numerator and denominator.
example {R : Type u} [Ring R] (n : ℕ) (P : IsoCategory Rᵐᵒᵖ) :
    (exactStructure Rᵐᵒᵖ).loopComponentsKZeroEquiv
      (ZerothHomotopy.mk (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0)
        (classifyingSpacePoint (completionPair Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) P)))) =
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass P.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass (rankOnePower Rᵐᵒᵖ n).of :=
  completionToOriginalQLoops_stage_kZero R n P
