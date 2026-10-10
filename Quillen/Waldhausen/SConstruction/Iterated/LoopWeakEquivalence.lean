/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.RelativeCylinder
public import Quillen.Topology.HomotopyFiber.CylinderComparison
public import Quillen.Topology.HomotopyFiber.Homeomorph
public import Quillen.Topology.HomotopyGroups.WeakEquivalenceCancellation

/-!
# Weak equivalence of the original first iterated-S loop map

The specific realized cylinder map is identified with the original relative-tail fiber
comparison through the explicit displayed-cylinder homotopy. The genuine all-weak relative
total is contractible, so its actual loop inclusion is an equivalence. Cancellation proves
that the unchanged first loop structure map is weak in every finite degree, including
components. The source category is small; no additional cylinder or factorization premise
is supplied, since the accepted all-weak coproduct construction discharges that input.

This proves the first nontrivial structure-map comparison, not all higher-stage comparisons
or a nonconnective construction.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
open Fibration Fibration.RelativeRows
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- The original relative tail with the actual all-acyclic witness-forgetting map. -/
def relativeProjection : C(|TheoremA.diagonalSSet (relativeSRows (AllWeak.nested W))|,
    doubleDelooping W) :=
  (AllWeak.ordinaryTotalInclusionMap W).comp (totalTailMap (AllWeak.nested W))

lemma relativeProjection_eq : relativeProjection W = (SSet.toTop.map (relativeTail W)).hom := by
  simp only [relativeProjection, relativeTail, CategoryTheory.Functor.map_comp, TopCat.hom_comp]
  rfl

lemma relativeProjection_point : relativeProjection W (totalBasepoint (AllWeak.nested W)) =
    doubleBasepoint W := by
  change AllWeak.ordinaryTotalInclusionMap W
    (totalTailMap (AllWeak.nested W) (totalBasepoint (AllWeak.nested W))) = _
  rw [totalTailMap_basepoint, AllWeak.ordinaryTotalInclusionMap_basepoint]
  rfl

lemma relativeProjection_fiberInclusion (x : W.Delooping) :
    relativeProjection W (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W)) x) =
      doubleBasepoint W := by
  change AllWeak.ordinaryTotalInclusionMap W
    (totalTailMap (AllWeak.nested W) (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))
      x)) = _
  rw [totalTailMap_totalFiberInclusion, AllWeak.ordinaryTotalInclusionMap_basepoint]
  rfl

/-- The realized literal lift runs from the actual relative zero to the original fiber inclusion. -/
def relativeTopHomotopy :
    (ContinuousMap.const W.Delooping (totalBasepoint (AllWeak.nested W))).Homotopy
      (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom where
  toContinuousMap := (realizationSimplicialHomotopy (relativeHomotopy W)).toContinuousMap
  map_zero_left x := ((realizationSimplicialHomotopy (relativeHomotopy W)).apply_zero x).trans
    (realization_const_apply _ x)
  map_one_left x := (realizationSimplicialHomotopy (relativeHomotopy W)).apply_one x

lemma cylinderLoop_eq_loopStructureMap :
    HomotopyFiber.cylinderLoop (relativeProjection W) (doubleBasepoint W)
      (totalBasepoint (AllWeak.nested W)) (relativeProjection_point W)
      (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
      (relativeProjection_fiberInclusion W) (relativeTopHomotopy W) = loopStructureMap W := by
  ext x t
  change relativeProjection W (realizationSimplicialHomotopy (relativeHomotopy W) (t,x)) =
    realizationSimplicialHomotopy (suspensionHomotopy W) (t,x)
  rw [relativeProjection_eq]
  have h := realizationSimplicialHomotopy_square (relativeHomotopy W) (suspensionHomotopy W)
    (𝟙 _) (relativeTail W) (by
      change relativeCylinder W ≫ relativeTail W = (𝟙 _ ▷ Δ[1]) ≫ suspensionCylinder W
      simpa using relativeCylinder_tail W) t x
  simp only [CategoryTheory.Functor.map_id, TopCat.id_app] at h
  exact h

/-- The target-coordinate homeomorphism retains the original full fiber path. -/
def relativeFiberHomeomorph :
    HomotopyFiber (totalTailMap (AllWeak.nested W))
      (ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested W))) ≃ₜ
        HomotopyFiber (relativeProjection W) (doubleBasepoint W) :=
  (HomotopyFiber.homeomorphOfSquare (totalTailMap (AllWeak.nested W)) (relativeProjection W)
    (Homeomorph.refl _) (AllWeak.ordinaryTotalHomeomorph W) rfl _).trans
      (HomotopyFiber.congrHomeomorph rfl (AllWeak.ordinaryTotalInclusionMap_basepoint W))

lemma relativeFiberHomeomorph_comparison :
    (relativeFiberHomeomorph W : C(_, _)).comp (totalTailFiberComparison (AllWeak.nested W)) =
      HomotopyFiber.cylinderStrictLift (relativeProjection W) (doubleBasepoint W)
        (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
        (relativeProjection_fiberInclusion W) := by
  ext x : 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · ext t
    exact AllWeak.ordinaryTotalInclusionMap_basepoint W

lemma relativeStrictComparison_weak :
    IsWeakHomotopyEquivalence
      (HomotopyFiber.cylinderStrictLift (relativeProjection W) (doubleBasepoint W)
        (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
        (relativeProjection_fiberInclusion W)) := by
  rw [← relativeFiberHomeomorph_comparison]
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv
    (relativeFiberHomeomorph W).toHomotopyEquiv).comp
      (totalTailFiberComparison_isWeakHomotopyEquivalence (AllWeak.nested W))

/-- The specific cylinder-defined loop map is a genuine weak equivalence. -/
theorem loopStructureMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (loopStructureMap W) := by
  let := AllWeak.relativeTotal_contractible W
  have H := HomotopyFiber.cylinderFiberHomotopy (relativeProjection W) (doubleBasepoint W)
    (totalBasepoint (AllWeak.nested W)) (relativeProjection_point W)
    (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
    (relativeProjection_fiberInclusion W) (relativeTopHomotopy W)
  rw [cylinderLoop_eq_loopStructureMap] at H
  have hc := (relativeStrictComparison_weak W).of_homotopy H.symm
  have hi := isWeakHomotopyEquivalence_of_homotopyEquiv
    (HomotopyFiber.loopInclusionEquivOfContractibleSource (relativeProjection W)
      (doubleBasepoint W) (totalBasepoint (AllWeak.nested W)) (relativeProjection_point W))
  rw [HomotopyFiber.loopInclusionEquivOfContractibleSource_toFun] at hi
  exact hc.of_comp_right hi

/-- The original based loop map is bijective in every homotopy degree, including zero. -/
theorem loopStructureMap_bijective (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (loopStructureMap W)
      (loopStructureMap_basepoint W)) := by
  have h : ∀ (y : Path (doubleBasepoint W) (doubleBasepoint W))
      (hy : loopStructureMap W W.kBasepoint = y),
      Function.Bijective (homotopyGroupMap (N := Fin n) (loopStructureMap W) hy) := by
    intro y hy
    cases hy
    exact (loopStructureMap_isWeakHomotopyEquivalence W).homotopy_bijective W.kBasepoint n
  exact h _ (loopStructureMap_basepoint W)

/-- The unchanged degree-raising homomorphism is an isomorphism on original K-groups. -/
theorem degreeRaisingMap_bijective (n : ℕ) : Function.Bijective (degreeRaisingMap W n) :=
  (loopShiftMulEquiv n).symm.bijective.comp (loopStructureMap_bijective W (n+1))

/-- The actual K-group comparison retains the original degree-raising forward map. -/
def degreeRaisingEquiv (n : ℕ) :
    W.K n ≃* HomotopyGroup.Pi (n+2) (doubleDelooping W) (doubleBasepoint W) :=
  MulEquiv.ofBijective (degreeRaisingMap W n) (degreeRaisingMap_bijective W n)

end Quillen.Waldhausen.IteratedS
