/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.FiberLiftHomotopyNaturality

/-! # Whole-track regression tests for homotopy-compatible specified fiber lifts -/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace QuillenTest.FiberLiftHomotopyNaturality

variable {S A O S' A' O' : LoopPrespectrum.{u}}
    (f : S ⟶ A) (r : A ⟶ O) (f' : S' ⟶ A') (r' : A' ⟶ O')
    (N : LoopPrespectrum.Homotopy (f ≫ r) (zeroHom S O))
    (N' : LoopPrespectrum.Homotopy (f' ≫ r') (zeroHom S' O'))
    (s : S ⟶ S') (a : A ⟶ A') (o : O ⟶ O')
    (Hf : LoopPrespectrum.Homotopy (f ≫ a) (s ≫ f'))
    (Hr : LoopPrespectrum.Homotopy (a ≫ r') (r ≫ o))
    (Q : (homotopyFiberLiftSquareNullHomotopy f r r' N a o Hr).Square
      (homotopyFiberLiftTargetNullHomotopy f' r' N' s)
      (Hf.postcomp r') (LoopPrespectrum.Homotopy.refl (zeroHom S O')))

/-- The original first half at comparison time zero is the supplied second-arrow track. -/
theorem original_first_half (n : ℕ) (x : S.space n) (t : unitInterval) :
    ((homotopyFiberLiftNaturalityHomotopy f r f' r' N N' s a o Hf Hr Q).level n
      (0, x)).1.2 ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩ =
      Hr.level n (t, f.map n x) := by
  rw [(homotopyFiberLiftNaturalityHomotopy f r f' r' N N' s a o Hf Hr Q).at_zero]
  exact homotopyFiberSquareMap_first_half r r' a o Hr n
    ((homotopyFiberLift r f N).map n x) t

/-- Comparison time one recovers the entire target chosen null at the original null time. -/
theorem original_target_null (n : ℕ) (x : S.space n) (t : unitInterval) :
    ((homotopyFiberLiftNaturalityHomotopy f r f' r' N N' s a o Hf Hr Q).level n
      (1, x)).1.2 t = N'.level n (t, s.map n x) := by
  rw [(homotopyFiberLiftNaturalityHomotopy f r f' r' N N' s a o Hf Hr Q).at_one]
  rfl

/-- Comparison time, null time, and structure time remain independent in the lifted path. -/
theorem independent_structure_time (n : ℕ) (c t v : unitInterval) (x : S.space n) :
    ((homotopyFiberLiftNaturalityHomotopy f r f' r' N N' s a o Hf Hr Q).level (n + 1)
      (c, S.structureMap n x v)).1.2 t =
      O'.structureMap n (Q.level n (c, (t, x))) v :=
  Q.comm n c t x v

include Hf Hr Q in
/-- Stability of the original source lift gives bijectivity of the target lift in degree zero. -/
theorem target_lift_zero_bijective (hs : IsStableEquivalence s)
    (ha : IsStableEquivalence a) (ho : IsStableEquivalence o)
    (h : IsStableEquivalence (homotopyFiberLift r f N)) :
    Function.Bijective ((stableHomotopyFunctor 0).map (homotopyFiberLift r' f' N')) :=
  (ConcreteCategory.isIso_iff_bijective _).mp
    ((homotopyFiberLift_homotopySquare_isStableEquivalence_iff
      f r f' r' N N' s a o Hf Hr Q hs ha ho).mp h 0)

include Hf Hr Q in
/-- The same supplied null square preserves the original zero-to-negative-one boundary. -/
theorem zero_negative_boundary
    [IsIso ((stableHomotopyFunctor (-1)).map (homotopyFiberLift r f N))]
    [IsIso ((stableHomotopyFunctor (-1)).map (homotopyFiberLift r' f' N'))] :
    stableFiberLiftConnecting f r N (-1) ≫ (stableHomotopyFunctor (-1)).map s =
      (stableHomotopyFunctor ((-1 : ℤ) + 1)).map o ≫ stableFiberLiftConnecting f' r' N' (-1) := by
  exact stableFiberLiftConnecting_homotopySquare
    f r f' r' N N' s a o Hf Hr Q (-1)

end QuillenTest.FiberLiftHomotopyNaturality
