/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-! Pasting three radial squares with their literal path-concatenation endpoints. -/
@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Path.Homotopy.ThreeRadialSquares
variable {S : Type*} [TopologicalSpace S]

/-- Cancel a reversed radial path followed by its original path. -/
def cancelLeft {o a b : S} (A : Path o a) (Y : Path a b) :
    (A.symm.trans (A.trans Y)).Homotopy Y :=
  (transAssoc A.symm A Y).symm.trans
    (((reflSymmTrans A).symm.hcomp (refl Y)).trans (reflTrans Y))

/-- Cancel a radial path followed by its reversal. -/
def cancelRight {o a b : S} (A : Path o a) (Y : Path o b) :
    (A.trans (A.symm.trans Y)).Homotopy Y :=
  (transAssoc A A.symm Y).symm.trans
    (((reflTransSymm A).symm.hcomp (refl Y)).trans (reflTrans Y))

/-- Remove the same radial prefix from the two sides of a comparison word. -/
def removeRadial {o a b c : S} (A : Path o a)
    (X : Path a b) (Y : Path a c) :
    ((A.trans X).symm.trans (A.trans Y)).Homotopy (X.symm.trans Y) :=
  ((transAssoc X.symm A.symm (A.trans Y)).trans
    ((refl X.symm).hcomp (cancelLeft A Y))).cast
      (congrArg (fun p ↦ p.trans (A.trans Y)) (Path.trans_symm A X).symm) rfl

/-- Cancel the repeated middle radial word in two concatenated comparisons. -/
def splice {o a b c : S} (P : Path o a) (Q : Path o b) (R : Path o c) :
    ((P.symm.trans Q).trans (Q.symm.trans R)).Homotopy (P.symm.trans R) :=
  (transAssoc P.symm Q (Q.symm.trans R)).trans
    ((refl P.symm).hcomp (cancelRight Q R))

/-- Three whole radial squares give the stated literal two-piece boundary comparison. -/
def paste {o a b c d z₀ z₁ z₂ : S}
    (A : Path o a) (B : Path o b) (C : Path o c) (D : Path o d)
    (X : Path a z₀) (Y : Path b z₀) (Z : Path b z₁) (W : Path c z₁)
    (V : Path c z₂) (U : Path d z₂)
    (J₁ : (A.trans X).Homotopy (B.trans Y))
    (J₂ : (C.trans W).Homotopy (B.trans Z))
    (J₃ : (C.trans V).Homotopy (D.trans U)) :
    ((Y.symm.trans Z).trans (W.symm.trans V)).Homotopy
      (X.symm.trans ((A.symm.trans D).trans U)) := by
  let first : (Y.symm.trans Z).Homotopy ((A.trans X).symm.trans (C.trans W)) :=
    (removeRadial B Y Z).symm.trans (J₁.symm.symm₂.hcomp J₂.symm)
  let second : (W.symm.trans V).Homotopy ((C.trans W).symm.trans (D.trans U)) :=
    (removeRadial C W V).symm.trans ((refl (C.trans W).symm).hcomp J₃)
  let last : ((A.trans X).symm.trans (D.trans U)).Homotopy
      (X.symm.trans ((A.symm.trans D).trans U)) :=
    ((transAssoc X.symm A.symm (D.trans U)).trans
      ((refl X.symm).hcomp (transAssoc A.symm D U).symm)).cast
        (congrArg (fun p ↦ p.trans (D.trans U)) (Path.trans_symm A X).symm) rfl
  exact (first.hcomp second).trans ((splice (A.trans X) (C.trans W) (D.trans U)).trans last)

end Path.Homotopy.ThreeRadialSquares
