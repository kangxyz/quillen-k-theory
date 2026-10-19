/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.FiniteLoopStableSign

/-! Low-rank signs test the actual fixed reversal words in every integer degree. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.LoopPrespectrum.FiniteLoopWords
universe u v w
namespace QuillenTest.FiniteLoopStableSign
variable {C : Type u} [Category.{v} C] (F : C ⥤ Quillen.LoopPrespectrum.{w})
  (X : C) (d : ℤ)

/-- The original two-loop reversal agrees with the genuine transpose sign. -/
theorem two : (stableHomotopyFunctor d).map ((reversalIso 2 F).hom.app X) = -𝟙 _ := by
  have h := reversalIso_stable_sign 2 F X d
  norm_num [Nat.choose] at h
  exact h

/-- The actual three-loop word remains negative. -/
theorem three : (stableHomotopyFunctor d).map ((reversalIso 3 F).hom.app X) = -𝟙 _ := by
  have h := reversalIso_stable_sign 3 F X d
  norm_num [Nat.choose] at h
  exact h

/-- The six crossings of the actual four-loop reversal produce the identity. -/
theorem four : (stableHomotopyFunctor d).map ((reversalIso 4 F).hom.app X) = 𝟙 _ := by
  have h := reversalIso_stable_sign 4 F X d
  norm_num [Nat.choose] at h
  exact h

end QuillenTest.FiniteLoopStableSign
