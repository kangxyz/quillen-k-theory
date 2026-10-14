/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MFiveScalarPaths
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MVertexNativeCells

/-! Whole original reassociation lifts after an actual native target map. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PostmappedSimplexLift

private theorem mp_level {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H H' K : Homotopy f g} (e : H = H')
    (p : H.RelHomotopy K = H'.RelHomotopy K) (J : H.RelHomotopy K) (n : ℕ) :
    ((p.mp J).level n).toContinuousMap = (J.level n).toContinuousMap := by
  subst H'
  rfl

private theorem associativity_level {E F : LoopPrespectrum.{u}}
    {f g h k : E ⟶ F} (H : Homotopy f g) (K : Homotopy g h) (L : Homotopy h k) (n : ℕ) :
    ((Homotopy.RelHomotopy.transAssoc H K L).level n).toContinuousMap =
      (((Homotopy.RelHomotopy.reparam (H.trans (K.trans L))
        SimplexParameters.rectangleAssociativityTime
        SimplexParameters.rectangleAssociativityTime_zero
        SimplexParameters.rectangleAssociativityTime_one).symm).level n).toContinuousMap := by
  unfold Homotopy.RelHomotopy.transAssoc
  dsimp only
  apply mp_level
  apply LoopPrespectrum.Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  have he := Path.Homotopy.trans_assoc_reparam (H.path n x) (K.path n x) (L.path n x)
  simp only [← Homotopy.path_trans] at he
  exact (DFunLike.congr_fun he s).symm

variable {V W : Model.{u}} {F : LoopPrespectrum.{u}} {k : ℕ}
  (S : ModelSimplex V W k) (B : F ⟶ prespectrum W)
  {a b c d : StdSimplex ℝ (Fin (k + 1))}
  {f g h j : prespectrum V ⟶ F}

/-- Equality to an original native path before its prescribed target map. -/
def PathLift (p : Path a b) (H : Homotopy f g) : Prop :=
  ∀ n t x, prespectrumSimplexFamily S n (p t, x) = B.map n (H.level n (t, x))

/-- Equality to the original two-parameter family before its prescribed target map. -/
def HomotopyLift {p q : Path a b} (J : p.Homotopy q)
    {H K : Homotopy f g} (M : H.RelHomotopy K) : Prop :=
  ∀ n r s x, prespectrumSimplexFamily S n (J (r, s), x) = B.map n (M.level n (r, (s, x)))

theorem PathLift.trans {p : Path a b} {q : Path b c}
    {H : Homotopy f g} {K : Homotopy g h}
    (hp : PathLift S B p H) (hq : PathLift S B q K) :
    PathLift S B (p.trans q) (H.trans K) := by
  intro n t x
  change prespectrumSimplexFamily S n ((p.trans q) t, x) =
    B.map n (((H.levelHomotopy n).trans (K.levelHomotopy n)) (t, x))
  rw [Path.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> first | exact hp n _ x | exact hq n _ x

theorem PathLift.refl {p : Path a b} {H : Homotopy f g} (hp : PathLift S B p H) :
    HomotopyLift S B (Path.Homotopy.refl p) (Homotopy.RelHomotopy.refl H) := by
  intro n r s x
  exact hp n s x

theorem HomotopyLift.symm {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift S B J M) :
    HomotopyLift S B J.symm M.symm := by
  intro n r s x
  exact hJ n (unitInterval.symm r) s x

theorem HomotopyLift.trans {p q z : Path a b} {J : p.Homotopy q} {K : q.Homotopy z}
    {H H' H'' : Homotopy f g} {M : H.RelHomotopy H'} {N : H'.RelHomotopy H''}
    (hJ : HomotopyLift S B J M) (hK : HomotopyLift S B K N) :
    HomotopyLift S B (J.trans K) (M.trans N) := by
  intro n r s x
  change prespectrumSimplexFamily S n ((J.trans K) (r, s), x) =
    B.map n (((M.level n).trans (N.level n)) (r, (s, x)))
  rw [Path.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> first | exact hJ n _ s x | exact hK n _ s x

private theorem hcomp_apply {H H' : Homotopy f g} {K K' : Homotopy g h}
    (J : H.RelHomotopy H') (L : K.RelHomotopy K') (n : ℕ) (r s : unitInterval)
    (x : (prespectrum V).space n) :
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
    (hJ : HomotopyLift S B J M) (hK : HomotopyLift S B K N) :
    HomotopyLift S B (J.hcomp K) (M.hcomp N) := by
  intro n r s x
  rw [Path.Homotopy.hcomp_apply, hcomp_apply]
  split <;> first | exact hJ n r _ x | exact hK n r _ x

/-- The actual dyadic associator is retained under the original target map. -/
theorem PathLift.transAssoc {p : Path a b} {q : Path b c} {z : Path c d}
    {H : Homotopy f g} {K : Homotopy g h} {L : Homotopy h j}
    (hp : PathLift S B p H) (hq : PathLift S B q K) (hz : PathLift S B z L) :
    HomotopyLift S B (Path.Homotopy.transAssoc p q z)
      (Homotopy.RelHomotopy.transAssoc H K L) := by
  intro n r s x
  change prespectrumSimplexFamily S n (Path.Homotopy.transAssoc p q z (r, s), x) =
    B.map n (((Homotopy.RelHomotopy.transAssoc H K L).level n).toContinuousMap (r, (s, x)))
  rw [associativity_level]
  exact (PathLift.trans S B hp (PathLift.trans S B hq hz)) n _ x

end Quillen.PostmappedSimplexLift
