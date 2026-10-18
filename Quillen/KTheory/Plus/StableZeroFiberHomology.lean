/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Plus.StableGeneralLinearPlus
public import Quillen.KTheory.Plus.ProjectiveCompletionCover
public import Quillen.Topology.Covering.PullbackFiber
public import Quillen.Topology.LocalCoefficients.PullbackCoveringHomologyUniverseLift

/-!
# Original stable-zero cover geometry and integral homology

The original plus certificate supplies raw Pi-one surjectivity and its exact
perfect kernel by cancelling the prescribed basepoint-path transport. The
actual pullback of any supplied simply connected covering consequently is
path connected and has perfect original Pi one. The original all-target-system
chain equivalences give a quasi-isomorphism on the literal second projection's
integral singular chains, in the actual successor universe.

The actual mapAt comparison of homotopy fibers lands directly over the raw
image of the original stable vertex, at its canonical constant-path basepoint.
Its original projection and connecting equations are retained. An actual
cover-existence theorem supplies all the data in the final existence witness;
no desired Pi-one or chain law is an input there.

This is the geometric and homological setup for a separate low-degree
fiber-perfectness criterion. It does not assert that the stable fiber is
perfect, that the pullback is simply connected, or a Matsumoto comparison.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory
open scoped Topology
namespace Quillen.FiniteProjectiveModule.StableCompletion

private theorem piOne_kernel_eq_raw {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (g : C(A, B)) {x : A} {y : B} (h : g x = y) :
    (piMap 0 g h).ker = (piMap 0 g (x := x) rfl).ker := by
  subst y
  rfl

private theorem piOne_surjective_of_raw {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (g : C(A, B)) {x : A} {y : B} (h : g x = y)
    (hg : Function.Surjective (piMap 0 g (x := x) rfl)) :
    Function.Surjective (piMap 0 g h) := by
  subst y
  exact hg

private theorem pullbackFiberMap_bijective_at
    {X : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E] [SimplyConnectedSpace E]
    (g : C(X, Y)) (q : C(E, Y)) (hq : IsCoveringMap q)
    (z : Covering.Pullback.Space g q) {y : Y} (hy : q z.val.2 = y) (hg : g z.val.1 = y) :
    Function.Bijective (piMap 0
      (HomotopyFiber.mapAt (Covering.Pullback.projection g q) q (Covering.Pullback.square g q)
        z.val.2 y hy)
      (HomotopyFiber.mapAt_basepoint (Covering.Pullback.projection g q) q
        (Covering.Pullback.square g q) z z.val.2 z.val.1 y rfl hg rfl hy)) := by
  subst y
  exact Covering.Pullback.fiberPiOneMap_bijective g q hq z

variable (R : Type u) [Ring R]

/-- The original plus certificate gives surjectivity before its prescribed basepoint transport. -/
theorem stableZeroMap_rawPiOne_surjective :
    Function.Surjective (piMap 0 (stableZeroMap R) (x := stableBase R) rfl) := by
  intro a
  obtain ⟨b, hb⟩ := (stableZeroMap_isPlusConstruction R).surjective
    (pathTransportMulEquiv (basepointPath R) 0 a)
  refine ⟨b, (pathTransportMulEquiv (basepointPath R) 0).injective ?_⟩
  exact hb

/-- Injectivity of the original basepoint transport retains exactly the original perfect kernel. -/
theorem stableZeroMap_rawPiOne_kernel :
    (piMap 0 (stableZeroMap R) (x := stableBase R) rfl).ker = stableElementaryPiOneSubgroup R := by
  rw [← (stableZeroMap_isPlusConstruction R).kernelEq]
  ext a
  change piMap 0 (stableZeroMap R) rfl a = 1 ↔
    pathTransportMulEquiv (basepointPath R) 0 (piMap 0 (stableZeroMap R) rfl a) = 1
  exact (pathTransportMulEquiv (basepointPath R) 0).map_eq_one_iff.symm

variable {T : Type (u + 1)} [TopologicalSpace T] (q : C(T, ZeroComponent R))
  (e : T) (he : q e = stableZeroMap R (stableBase R))

/-- The displayed covering point paired with the original stable vertex, with no new base path. -/
def stableZeroCoverPoint : Covering.Pullback.Space (stableZeroMap R) q :=
  ⟨(stableBase R, e), he.symm⟩

variable (hq : IsCoveringMap q) [SimplyConnectedSpace T]

include hq e he in
/-- The literal cover pullback is path connected by original raw Pi-one surjectivity. -/
theorem stableZeroCoverPullback_pathConnectedSpace :
    PathConnectedSpace (Covering.Pullback.Space (stableZeroMap R) q) := by
  let : PathConnectedSpace
      (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))) :=
    (stableZeroMap_isPlusConstruction R).sourcePathConnected
  exact Covering.Pullback.pathConnectedSpace (stableZeroMap R) q hq
    (stableZeroCoverPoint R q e he)
      (piOne_surjective_of_raw (stableZeroMap R) he.symm (stableZeroMap_rawPiOne_surjective R))

include hq in
/-- The actual first-projection kernel equivalence constructs perfectness of the pullback Pi one. -/
theorem stableZeroCoverPullback_piOne_isPerfect :
    Group.IsPerfect (HomotopyGroup.Pi 1 (Covering.Pullback.Space (stableZeroMap R) q)
      (stableZeroCoverPoint R q e he)) := by
  have hk : (piMap 0 (stableZeroMap R) he.symm).ker = stableElementaryPiOneSubgroup R :=
    (piOne_kernel_eq_raw (stableZeroMap R) he.symm).trans (stableZeroMap_rawPiOne_kernel R)
  let : Group.IsPerfect
      (piMap 0 (stableZeroMap R) (stableZeroCoverPoint R q e he).property).ker := by
    change Group.IsPerfect (piMap 0 (stableZeroMap R) he.symm).ker
    exact hk.symm ▸ (stableZeroMap_isPlusConstruction R).perfect
  let c := Covering.Pullback.piOneKernelEquiv (stableZeroMap R) q hq
    (stableZeroCoverPoint R q e he)
  exact Group.IsPerfect.ofSurjective (f := c.symm.toMonoidHom) c.symm.surjective

omit [SimplyConnectedSpace T] in
/-- The actual map of fibers lands directly over the original raw image basepoint. -/
def stableZeroCoverFiberMap :
    C(HomotopyFiber (Covering.Pullback.lift (stableZeroMap R) q) e,
      HomotopyFiber (stableZeroMap R) (stableZeroMap R (stableBase R))) :=
  HomotopyFiber.mapAt (Covering.Pullback.projection (stableZeroMap R) q) q
    (Covering.Pullback.square (stableZeroMap R) q) e (stableZeroMap R (stableBase R)) he

omit [SimplyConnectedSpace T] in
/-- The original constant-path fiber basepoint is retained exactly. -/
theorem stableZeroCoverFiberMap_basepoint :
    stableZeroCoverFiberMap R q e he
      (HomotopyFiber.basepoint (Covering.Pullback.lift (stableZeroMap R) q) e
        (stableZeroCoverPoint R q e he) rfl) =
    HomotopyFiber.basepoint (stableZeroMap R) (stableZeroMap R (stableBase R))
      (stableBase R) rfl :=
  HomotopyFiber.mapAt_basepoint (Covering.Pullback.projection (stableZeroMap R) q) q
    (Covering.Pullback.square (stableZeroMap R) q)
    (stableZeroCoverPoint R q e he) e (stableBase R) (stableZeroMap R (stableBase R))
    rfl rfl rfl he

omit [SimplyConnectedSpace T] in
/-- The original fiber Pi-one map uses that exact map and constant-path basepoint equality. -/
def stableZeroCoverFiberPiOneMap :
    HomotopyGroup.Pi 1 (HomotopyFiber (Covering.Pullback.lift (stableZeroMap R) q) e)
        (HomotopyFiber.basepoint (Covering.Pullback.lift (stableZeroMap R) q) e
          (stableZeroCoverPoint R q e he) rfl) →*
      HomotopyGroup.Pi 1 (HomotopyFiber (stableZeroMap R) (stableZeroMap R (stableBase R)))
        (HomotopyFiber.basepoint (stableZeroMap R) (stableZeroMap R (stableBase R))
          (stableBase R) rfl) :=
  piMap 0 (stableZeroCoverFiberMap R q e he) (stableZeroCoverFiberMap_basepoint R q e he)

include hq in
/-- The actual fiber map is bijective on Pi one, without asserting perfectness of its target. -/
theorem stableZeroCoverFiberPiOneMap_bijective :
    Function.Bijective (stableZeroCoverFiberPiOneMap R q e he) :=
  pullbackFiberMap_bijective_at (stableZeroMap R) q hq (stableZeroCoverPoint R q e he) he rfl

/-- The resulting Pi-one equivalence retains the original map into the original stable fiber. -/
def stableZeroCoverFiberPiOneEquiv :
    HomotopyGroup.Pi 1 (HomotopyFiber (Covering.Pullback.lift (stableZeroMap R) q) e)
        (HomotopyFiber.basepoint (Covering.Pullback.lift (stableZeroMap R) q) e
          (stableZeroCoverPoint R q e he) rfl) ≃*
      HomotopyGroup.Pi 1 (HomotopyFiber (stableZeroMap R) (stableZeroMap R (stableBase R)))
        (HomotopyFiber.basepoint (stableZeroMap R) (stableZeroMap R (stableBase R))
          (stableBase R) rfl) :=
  MulEquiv.ofBijective (stableZeroCoverFiberPiOneMap R q e he)
    (stableZeroCoverFiberPiOneMap_bijective R q e he hq)

/-- Its forward homomorphism is the original actual mapAt map. -/
theorem stableZeroCoverFiberPiOneEquiv_apply
    (a : HomotopyGroup.Pi 1 (HomotopyFiber (Covering.Pullback.lift (stableZeroMap R) q) e)
      (HomotopyFiber.basepoint (Covering.Pullback.lift (stableZeroMap R) q) e
        (stableZeroCoverPoint R q e he) rfl)) :
    stableZeroCoverFiberPiOneEquiv R q e he hq a = stableZeroCoverFiberPiOneMap R q e he a := rfl


omit [SimplyConnectedSpace T] in
/-- The original fiber equivalence keeps the actual first-projection equation. -/
theorem stableZeroCoverFiberPiOneMap_projection :
    (piMap 0 (HomotopyFiber.projection (stableZeroMap R) (stableZeroMap R (stableBase R)))
      (HomotopyFiber.projection_basepoint (stableZeroMap R)
        (stableZeroMap R (stableBase R)) (stableBase R) rfl)).comp
          (stableZeroCoverFiberPiOneMap R q e he) =
      (piMap 0 (Covering.Pullback.projection (stableZeroMap R) q)
        (x := stableZeroCoverPoint R q e he) rfl).comp
          (piMap 0 (HomotopyFiber.projection (Covering.Pullback.lift (stableZeroMap R) q) e)
            (HomotopyFiber.projection_basepoint (Covering.Pullback.lift (stableZeroMap R) q) e
              (stableZeroCoverPoint R q e he) rfl)) :=
  HomotopyFiber.projectionHom_mapAt_natural
    (Covering.Pullback.projection (stableZeroMap R) q) q
      (Covering.Pullback.square (stableZeroMap R) q)
      (stableZeroCoverPoint R q e he) e rfl (stableBase R)
      (stableZeroMap R (stableBase R)) rfl he rfl 0

omit [SimplyConnectedSpace T] in
/-- The original connecting equation retains q and its displayed equality over the raw image. -/
theorem stableZeroCoverFiberPiOneMap_connecting :
    (stableZeroCoverFiberPiOneMap R q e he).comp
      (HomotopyFiber.connectingHom (Covering.Pullback.lift (stableZeroMap R) q) e
        (stableZeroCoverPoint R q e he) rfl 0) =
    (HomotopyFiber.connectingHom (stableZeroMap R) (stableZeroMap R (stableBase R))
      (stableBase R) rfl 0).comp (piMap 1 q he) :=
  HomotopyFiber.connectingHom_mapAt_natural
    (Covering.Pullback.projection (stableZeroMap R) q) q
      (Covering.Pullback.square (stableZeroMap R) q)
      (stableZeroCoverPoint R q e he) e (stableBase R)
      (stableZeroMap R (stableBase R)) rfl rfl rfl he 0


omit [SimplyConnectedSpace T] in
include hq in
open LocalCoefficients.PullbackCoveringUniverseLift in
/-- The original integral chain map of the literal second projection is a quasi-isomorphism. -/
theorem stableZeroCoverLift_quasiIso :
    QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u + 1} ℤ)).obj
      LocalCoefficients.integralCoefficients).map
        (TopCat.ofHom (Covering.Pullback.lift (stableZeroMap R) q))) :=
  successor_singular_quasiIso_of_all_localCoefficients
    (stableZeroMap R) hq (stableZeroMap_isPlusConstruction R).localCoefficients

/-- Every ring has actual covering data with all geometric and homological setup properties
constructed for the original stable map and its original constant-path fiber basepoint. -/
theorem exists_stableZeroCover_homologicalSetup :
    ∃ T : Type (u + 1), ∃ t : TopologicalSpace T,
      letI := t
      ∃ q : C(T, ZeroComponent R), ∃ e : T,
        ∃ he : q e = stableZeroMap R (stableBase R),
          IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace T ∧
          PathConnectedSpace (Covering.Pullback.Space (stableZeroMap R) q) ∧
          Group.IsPerfect (HomotopyGroup.Pi 1 (Covering.Pullback.Space (stableZeroMap R) q)
            (stableZeroCoverPoint R q e he)) ∧
          QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u + 1} ℤ)).obj
            LocalCoefficients.integralCoefficients).map
              (TopCat.ofHom (Covering.Pullback.lift (stableZeroMap R) q))) ∧
          Function.Bijective (stableZeroCoverFiberPiOneMap R q e he) := by
  obtain ⟨T, t, q, hq, hqs, hT⟩ := exists_simplyConnected_zeroComponent_cover R
  let := t
  let := hT
  obtain ⟨e, he⟩ := hqs (stableZeroMap R (stableBase R))
  exact ⟨T, t, q, e, he, hq, hqs, hT,
    stableZeroCoverPullback_pathConnectedSpace R q e he hq,
    stableZeroCoverPullback_piOne_isPerfect R q e he hq,
    stableZeroCoverLift_quasiIso R q hq,
    stableZeroCoverFiberPiOneMap_bijective R q e he hq⟩

end Quillen.FiniteProjectiveModule.StableCompletion
