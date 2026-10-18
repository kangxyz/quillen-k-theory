/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.RelativeHomotopyConjugationEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyAssociatorEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyTerminalEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyEndpointEvaluation
public import Quillen.Topology.Path.NullWordEvaluation

/-!
# Whole-value lifts through an arbitrary evaluator

These operation lemmas retain the literal native clocks. The evaluator need not be continuous.
They provide the common proof interface for simplex and chosen-carrier projection-square pastes.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Quillen.NativeParameterEvaluation
open LoopPrespectrum
variable {X : Type v} [TopologicalSpace X] {E F : LoopPrespectrum.{u}}
  (ev : ∀ n, X × E.space n → F.space n) {a b c d : X} {f g h j : E ⟶ F}

/-- Pointwise equality with the specified whole native track, with its endpoints left unchanged. -/
def PathLift (p : Path a b) (H : Homotopy f g) : Prop :=
  ∀ n t x, ev n (p t, x) = H.level n (t, x)

/-- Pointwise equality with a specified whole native relative comparison. -/
def HomotopyLift {p q : Path a b} (J : p.Homotopy q)
    {H K : Homotopy f g} (M : H.RelHomotopy K) : Prop :=
  ∀ n r s x, ev n (J (r, s), x) = M.level n (r, (s, x))

theorem HomotopyLift.source {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift ev J M) :
    PathLift ev p H := by
  intro n t x
  calc
    ev n (p t, x) =
        ev n (J (0, t), x) := by rw [J.apply_zero]; rfl
    _ = M.level n (0, (t, x)) := hJ n 0 t x
    _ = H.level n (t, x) := (M.level n).apply_zero _

theorem HomotopyLift.target {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift ev J M) :
    PathLift ev q K := by
  intro n t x
  calc
    ev n (q t, x) =
        ev n (J (1, t), x) := by rw [J.apply_one]; rfl
    _ = M.level n (1, (t, x)) := hJ n 1 t x
    _ = K.level n (t, x) := (M.level n).apply_one _

theorem PathLift.refl {p : Path a b} {H : Homotopy f g} (hp : PathLift ev p H) :
    HomotopyLift ev (Path.Homotopy.refl p) (Homotopy.RelHomotopy.refl H) := by
  intro n r s x
  exact hp n s x

/-- Whole-level endpoint transport in the existing API changes no scalar lift. -/
theorem HomotopyLift.ofLevels {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift ev J M)
    {f' g' : E ⟶ F} (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n) :
    HomotopyLift ev J (Homotopy.RelHomotopy.ofLevels M H' K' hH hK) := hJ

theorem PathLift.symm {p : Path a b} {H : Homotopy f g} (hp : PathLift ev p H) :
    PathLift ev p.symm H.symm := by
  intro n t x
  exact hp n (unitInterval.symm t) x

theorem PathLift.trans {p : Path a b} {q : Path b c}
    {H : Homotopy f g} {K : Homotopy g h} (hp : PathLift ev p H) (hq : PathLift ev q K) :
    PathLift ev (p.trans q) (H.trans K) := by
  intro n t x
  change ev n ((p.trans q) t, x) =
    ((H.levelHomotopy n).trans (K.levelHomotopy n)) (t, x)
  rw [Path.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> first | exact hp n _ x | exact hq n _ x

theorem HomotopyLift.symm {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift ev J M) :
    HomotopyLift ev J.symm M.symm := by
  intro n r s x
  exact hJ n (unitInterval.symm r) s x

theorem HomotopyLift.symmPath {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift ev J M) :
    HomotopyLift ev J.symm₂ M.symmPath := by
  intro n r s x
  exact hJ n r (unitInterval.symm s) x

theorem HomotopyLift.trans {p q z : Path a b} {J : p.Homotopy q} {K : q.Homotopy z}
    {H H' H'' : Homotopy f g} {M : H.RelHomotopy H'} {N : H'.RelHomotopy H''}
    (hJ : HomotopyLift ev J M) (hK : HomotopyLift ev K N) :
    HomotopyLift ev (J.trans K) (M.trans N) := by
  intro n r s x
  change ev n ((J.trans K) (r, s), x) =
    ((M.level n).trans (N.level n)) (r, (s, x))
  rw [Path.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> first | exact hJ n _ s x | exact hK n _ s x

private theorem relative_hcomp_apply {H H' : Homotopy f g} {K K' : Homotopy g h}
    (J : H.RelHomotopy H') (L : K.RelHomotopy K') (n : ℕ) (r s : unitInterval)
    (x : (E).space n) :
    (J.hcomp L).level n (r, (s, x)) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        J.level n (r, (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x))
      else L.level n (r, (⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

theorem HomotopyLift.hcomp {p q : Path a b} {p' q' : Path b c}
    {J : p.Homotopy q} {K : p'.Homotopy q'}
    {H H' : Homotopy f g} {L L' : Homotopy g h}
    {M : H.RelHomotopy H'} {N : L.RelHomotopy L'}
    (hJ : HomotopyLift ev J M) (hK : HomotopyLift ev K N) :
    HomotopyLift ev (J.hcomp K) (M.hcomp N) := by
  intro n r s x
  rw [Path.Homotopy.hcomp_apply, relative_hcomp_apply]
  split <;> first | exact hJ n r _ x | exact hK n r _ x

/-- The native linear reparameterization comparison keeps its exact scalar parameter formula. -/
theorem PathLift.reparam {p : Path a b} {H : Homotopy f g} (hp : PathLift ev p H)
    (φ : C(unitInterval, unitInterval)) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    HomotopyLift ev (Path.Homotopy.reparam p φ φ.continuous h0 h1)
      (Homotopy.RelHomotopy.reparam H φ h0 h1) := by
  intro n r s x
  exact hp n _ x

/-- The native cancellation comparison keeps its exact old contraction parameter. -/
theorem PathLift.reflTransSymm {p : Path a b} {H : Homotopy f g}
    (hp : PathLift ev p H) :
    HomotopyLift ev (Path.Homotopy.reflTransSymm p) (Homotopy.RelHomotopy.reflTransSymm H) := by
  intro n r s x
  exact hp n _ x

/-- Reassociation retains the exact native clock under any whole-value evaluator. -/
theorem PathLift.transAssoc {p : Path a b} {q : Path b c} {z : Path c d}
    {H : Homotopy f g} {K : Homotopy g h} {L : Homotopy h j}
    (hp : PathLift ev p H) (hq : PathLift ev q K) (hz : PathLift ev z L) :
    HomotopyLift ev (Path.Homotopy.transAssoc p q z)
      (Homotopy.RelHomotopy.transAssoc H K L) := by
  intro n r s x
  rw [Homotopy.RelHomotopy.transAssoc_apply_path]
  exact Path.Evaluation.transAssoc (fun y ↦ ev n (y, x)) p q z
    (H.path n x) (K.path n x) (L.path n x)
    (fun t ↦ hp n t x) (fun t ↦ hq n t x) (fun t ↦ hz n t x) r s

/-- Terminal-pause cancellation retains its whole prescribed value. -/
theorem PathLift.transRefl {p : Path a b} {H : Homotopy f g} (hp : PathLift ev p H) :
    HomotopyLift ev (Path.Homotopy.transRefl p) (Homotopy.RelHomotopy.transRefl H) := by
  intro n r s x
  rw [Homotopy.RelHomotopy.transRefl_apply_path]
  exact hp n _ x

/-- Initial-pause cancellation retains its whole prescribed value. -/
theorem PathLift.reflTrans {p : Path a b} {H : Homotopy f g} (hp : PathLift ev p H) :
    HomotopyLift ev (Path.Homotopy.reflTrans p) (Homotopy.RelHomotopy.reflTrans H) := by
  intro n r s x
  rw [Homotopy.RelHomotopy.reflTrans_apply_path]
  exact Path.Evaluation.reflTrans (fun y ↦ ev n (y, x)) p (H.path n x)
    (fun t ↦ hp n t x) r s

/-- Reverse cancellation retains its endpoint transport and both time coordinates. -/
theorem PathLift.reflSymmTrans {p : Path a b} {H : Homotopy f g} (hp : PathLift ev p H) :
    HomotopyLift ev
      ((Path.Homotopy.reflTransSymm p.symm).cast rfl
        (congrArg (fun q ↦ p.symm.trans q) (Path.symm_symm p)))
      (Homotopy.RelHomotopy.reflSymmTrans H) := by
  intro n r s x
  rw [Homotopy.RelHomotopy.reflSymmTrans_apply_path]
  exact hp n _ x

end Quillen.NativeParameterEvaluation
