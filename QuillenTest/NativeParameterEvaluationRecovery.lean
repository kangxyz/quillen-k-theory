/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.NativeParameterEvaluation

/-! Recovery regressions for null words under an arbitrary whole-value evaluator. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u v
namespace NativeParameterEvaluationRecovery
open NativeParameterEvaluation
variable {X : Type v} [TopologicalSpace X] {E F : LoopPrespectrum.{u}}
  (ev : ∀ n, X × E.space n → F.space n) {a b : X} {f g : E ⟶ F}

/-- A comparison determines the entire closed difference word, including its half clock. -/
theorem difference_word {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift ev J M)
    (n : ℕ) (t : I) (x : E.space n) :
    ev n ((p.trans q.symm) t, x) = (H.trans K.symm).level n (t, x) :=
  PathLift.trans ev (HomotopyLift.source ev hJ)
    (PathLift.symm ev (HomotopyLift.target ev hJ)) n t x

/-- Reversing both clocks commutes with exact whole-level endpoint transport. -/
theorem reversed_transport {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift ev J M)
    {f' g' : E ⟶ F} (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n)
    (n : ℕ) (r s : I) (x : E.space n) :
    ev n (J.symm.symm₂ (r, s), x) =
      ((M.ofLevels H' K' hH hK).symm.symmPath).level n (r, (s, x)) :=
  HomotopyLift.symmPath ev
    (HomotopyLift.symm ev (HomotopyLift.ofLevels ev hJ H' K' hH hK)) n r s x

#print axioms difference_word
#print axioms reversed_transport
#print axioms Quillen.NativeParameterEvaluation.PathLift.transAssoc
#print axioms Quillen.NativeParameterEvaluation.HomotopyLift.hcomp
#print axioms Quillen.NativeParameterEvaluation.PathLift.reflTransSymm
#print axioms Quillen.NativeParameterEvaluation.PathLift.reflSymmTrans
#print axioms Quillen.NativeParameterEvaluation.PathLift.transRefl
#print axioms Quillen.NativeParameterEvaluation.PathLift.reflTrans
#print axioms Quillen.NativeParameterEvaluation.PathLift.reparam
end NativeParameterEvaluationRecovery
