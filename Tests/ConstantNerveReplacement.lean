/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.CategoryTheory.TheoremA.ConstantNerveReplacement

/-! # The unchanged initial constant-diagram entry -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.TheoremA
open scoped Simplicial Topology
universe u
variable {D A : Type u} [SmallCategory D] [SmallCategory A]

example (i : D) (hi : IsInitial i) :
    ContinuousMap.HomotopyEquiv |nerve A|
      |replacementDiagonal ((Functor.const D).obj (nerve A))| :=
  constantNerveReplacementEntryHomotopyEquiv A i hi

example (i : D) (hi : IsInitial i) :
    (constantNerveReplacementEntryHomotopyEquiv A i hi).toFun =
      (SSet.toTop.map (replacementEntry ((Functor.const D).obj (nerve A)) i)).hom :=
  constantNerveReplacementEntryHomotopyEquiv_toFun A i hi

example (i : D) :
    replacementEntry ((Functor.const D).obj (nerve A)) i ≫
      (constantNerveReplacementIso A).hom = nerveMap (constantNerveEntryFunctor A i) :=
  constantNerveReplacementIso_entry A i
