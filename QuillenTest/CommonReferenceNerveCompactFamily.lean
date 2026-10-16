/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactFamily

/-! Whole original simplex recovery, independent loop/structure times, and exact supplied faces. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Convexity Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v w
namespace QuillenTest.CommonReferenceNerveCompactFamily
variable {V W : Model.{u}} (F : V ⟶ W)

/-- Every level and every original simplex coordinate recover the unchanged native family. -/
theorem whole_original_family {k : ℕ} (N : Fin (k + 1) → CommonReferenceNerve.Node F)
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    CommonReferenceNerve.compactPrespectrumFamily F (CommonReferenceNerve.parameter F N)
        n (z, x) = CommonReferenceNerve.prespectrumFamily F N n (z, x) :=
  CommonReferenceNerve.compactPrespectrumFamily_eq_simplex F
    (CommonReferenceNerve.parameter F N) N z z rfl n x

variable {T : Type v} [TopologicalSpace T] [CompactSpace T]
  (p : C(T, |nerve (Codiscrete (CommonReferenceNerve.Node F))|))

/-- The original point is retained at level zero and at every other level. -/
theorem original_point (n : ℕ) (t : T) :
    CommonReferenceNerve.compactPrespectrumFamily F p n (t, (prespectrum V).point n) =
      (prespectrum W).point n :=
  CommonReferenceNerve.compactPrespectrumFamily_point F p n t

/-- A compact parameter time never replaces the independent prespectrum structure coordinate. -/
theorem independent_structure (n : ℕ) (t : T) (x : (prespectrum V).space n)
    (s : unitInterval) :
    CommonReferenceNerve.compactPrespectrumFamily F p (n + 1)
        (t, (prespectrum V).structureMap n x s) =
      (prespectrum W).structureMap n
        (CommonReferenceNerve.compactPrespectrumFamily F p n (t, x)) s :=
  CommonReferenceNerve.compactPrespectrumFamily_structure F p n t x s

/-- The level-zero input loop retains its own independent coordinate, on every input loop. -/
theorem independent_input_loop (t : T) (γ : Path (stagePoint 0 V) (stagePoint 0 V))
    (s : unitInterval) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      CommonReferenceNerve.compactPrespectrumFamily F p 0 (t, γ)) s =
      CommonReferenceNerve.compactStageFamily F 0 p (t, γ s) :=
  CommonReferenceNerve.compactPrespectrumFamily_zero_apply F p t γ s

/-- Any supplied whole face recovers the old family; its face-index space need not be compact. -/
theorem supplied_whole_face {S : Type w} {k : ℕ}
    (N : Fin (k + 1) → CommonReferenceNerve.Node F) (h : S → T)
    (z : S → StdSimplex ℝ (Fin (k + 1)))
    (hz : ∀ q, p (h q) = CommonReferenceNerve.parameter F N (z q))
    (q : S) (n : ℕ) (x : (prespectrum V).space n) :
    CommonReferenceNerve.compactPrespectrumFamily F p n (h q, x) =
      CommonReferenceNerve.prespectrumFamily F N n (z q, x) :=
  CommonReferenceNerve.compactPrespectrumFamily_eq_simplex F p N (h q) (z q) (hz q) n x

end QuillenTest.CommonReferenceNerveCompactFamily
