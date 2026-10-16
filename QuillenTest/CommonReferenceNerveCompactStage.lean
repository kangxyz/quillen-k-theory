/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactStage

/-! Exact finite-carrier comparison, choice independence, and full old-simplex recovery. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Convexity Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology
universe u v
namespace QuillenTest.CommonReferenceNerveCompactStage

/-- The original comparison retains both native input and actual carrier inclusion. -/
theorem actual_comparison_inclusion (X Y : SSet.{u}) (B : Y.Subcomplex) [SSet.Finite B]
    (x : |X|) (b : |(B : SSet.{u})|) :
    Quillen.ProductRealization.comparison X Y
      (CommonReferenceNerve.carrierLift X Y B (x, b)) = (x, SSet.toTop.map B.ι b) :=
  CommonReferenceNerve.comparison_carrierLift X Y B x b

/-- Two independently supplied carriers represent exactly the same actual product point. -/
theorem independent_carrier_choices (X Y : SSet.{u}) (B C : Y.Subcomplex)
    [SSet.Finite B] [SSet.Finite C] (x : |X|)
    (b : |(B : SSet.{u})|) (c : |(C : SSet.{u})|)
    (h : SSet.toTop.map B.ι b = SSet.toTop.map C.ι c) :
    CommonReferenceNerve.carrierLift X Y B (x, b) =
      CommonReferenceNerve.carrierLift X Y C (x, c) :=
  CommonReferenceNerve.carrierLift_eq X Y B C x b c h

variable {V W : Model.{u}} (F : V ⟶ W)

/-- Every original simplex parameter and every native input are retained simultaneously. -/
theorem whole_original_simplex (r : ℕ) {k : ℕ} (N : Fin (k + 1) → CommonReferenceNerve.Node F)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : stageSpace r V) :
    CommonReferenceNerve.compactStageFamily F r (CommonReferenceNerve.parameter F N) (z, x) =
      CommonReferenceNerve.stageBarycentric F r N (z, x) :=
  CommonReferenceNerve.compactStageFamily_eq_simplex F r
    (CommonReferenceNerve.parameter F N) N z z rfl x

/-- An arbitrary exact compact parameter factorization recovers its entire stage family. -/
theorem supplied_compact_factorization {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (r : ℕ) (p : C(T, |nerve (Codiscrete (CommonReferenceNerve.Node F))|))
    (B : (nerve (Codiscrete (CommonReferenceNerve.Node F))).Subcomplex) [SSet.Finite B]
    (g : C(T, |(B : SSet)|)) (hg : (SSet.toTop.map B.ι).hom.comp g = p)
    (t : T) (x : stageSpace r V) :
    CommonReferenceNerve.compactStageFamily F r p (t, x) =
      CommonReferenceNerve.stageCarrierFamily F r B (g t, x) :=
  CommonReferenceNerve.compactStageFamily_eq_carrier F r p B g hg t x

end QuillenTest.CommonReferenceNerveCompactStage
