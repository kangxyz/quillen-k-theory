/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveWhiskering

/-! Named clients retain the actual whole nerve simplex, its complete references, and native
level zero under both directions of original whiskering. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor Convexity Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology
universe u
namespace QuillenTest.CommonReferenceNerveWhiskering
variable {V W T : Model.{u}} (F : V ⟶ W)

/-- The complete precomposed reference is the original left-whiskered transformation. -/
theorem original_precomp_reference (J : T ⟶ V) (N : CommonReferenceNerve.Node F) :
    (CommonReferenceNerve.precompNode J N).2 = isoWhiskerLeft J.functor N.2 := rfl

/-- The complete postcomposed reference is the original right-whiskered transformation. -/
theorem original_postcomp_reference (J : W ⟶ T) (N : CommonReferenceNerve.Node F) :
    (CommonReferenceNerve.postcompNode J N).2 = isoWhiskerRight N.2 J.functor := rfl

/-- The actual entire nerve simplex retains every ordered node, including its reference. -/
theorem original_postcomp_parameter {k : ℕ} (N : Fin (k + 1) → CommonReferenceNerve.Node F)
    (J : W ⟶ T) (z : StdSimplex ℝ (Fin (k + 1))) :
    CommonReferenceNerve.mapParameter (CommonReferenceNerve.postcompNode J)
        (CommonReferenceNerve.parameter F N z) =
      CommonReferenceNerve.parameter (F ≫ J)
        (fun i ↦ CommonReferenceNerve.postcompNode J (N i)) z :=
  CommonReferenceNerve.mapParameter_parameter _ N z

/-- Precomposition includes the original native input-loop level zero. -/
theorem original_precomp_level_zero {k : ℕ}
    (N : Fin (k + 1) → CommonReferenceNerve.Node F) (J : T ⟶ V)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum T).space 0) :
    CommonReferenceNerve.prespectrumFamily (J ≫ F)
        (fun i ↦ CommonReferenceNerve.precompNode J (N i)) 0 (z, x) =
      CommonReferenceNerve.prespectrumFamily F N 0 (z, (prespectrumMap J).map 0 x) :=
  CommonReferenceNerve.prespectrumFamily_precomp N J 0 z x

/-- Postcomposition includes the original native input-loop level zero. -/
theorem original_postcomp_level_zero {k : ℕ}
    (N : Fin (k + 1) → CommonReferenceNerve.Node F) (J : W ⟶ T)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space 0) :
    CommonReferenceNerve.prespectrumFamily (F ≫ J)
        (fun i ↦ CommonReferenceNerve.postcompNode J (N i)) 0 (z, x) =
      (prespectrumMap J).map 0 (CommonReferenceNerve.prespectrumFamily F N 0 (z, x)) :=
  CommonReferenceNerve.prespectrumFamily_postcomp N J 0 z x

end QuillenTest.CommonReferenceNerveWhiskering
