/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.LoopWeakEquivalence
public import Quillen.Waldhausen.SConstruction.Iterated.Prespectrum

/-! # Original-cylinder and original-K consumers for the first S-loop equivalence -/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
open Quillen Quillen.Waldhausen.IteratedS
universe u v w
namespace QuillenTest.IteratedSLoopEquivalence

open Quillen

/-- Independent point-space universes and both literal fiber-homotopy endpoints. -/
theorem actual_fiber_homotopy {X : Type u} {E : Type v} {B : Type w}
    [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) (b : B) (e : E) (he : p e = b) (g : C(X,E)) (hg : ∀ x, p (g x) = b)
    (H : (ContinuousMap.const X e).Homotopy g) (x : X) :
    HomotopyFiber.cylinderFiberHomotopy p b e he g hg H (0,x) =
      HomotopyFiber.loopInclusion p b e he (HomotopyFiber.cylinderLoop p b e he g hg H x) ∧
    HomotopyFiber.cylinderFiberHomotopy p b e he g hg H (1,x) =
      HomotopyFiber.basepoint p b (g x) (hg x) :=
  ⟨(HomotopyFiber.cylinderFiberHomotopy p b e he g hg H).apply_zero x,
    (HomotopyFiber.cylinderFiberHomotopy p b e he g hg H).apply_one x⟩

variable {C : Type u} [SmallCategory C] (W : Structure C)
open Fibration Fibration.RelativeRows

/-- The lifted original cylinder has both literal faces and the exact original projected cylinder.
  -/
theorem original_relative_faces :
    SSet.ι₀ ≫ relativeCylinder W = SSet.const (totalZeroVertex (AllWeak.nested W)) ∧
    SSet.ι₁ ≫ relativeCylinder W = totalFiberInclusion (AllWeak.nested W) ∧
    relativeCylinder W ≫ relativeTail W = suspensionCylinder W :=
  ⟨relativeCylinder_zero W, relativeCylinder_one W, relativeCylinder_tail W⟩

/-- The exact entire loop, rather than only its homotopy class, is the old structure map. -/
theorem original_projected_loop (x : W.Delooping) (t : unitInterval) :
    HomotopyFiber.cylinderLoop (relativeProjection W) (doubleBasepoint W)
      (totalBasepoint (AllWeak.nested W)) (relativeProjection_point W)
      (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
      (relativeProjection_fiberInclusion W) (relativeTopHomotopy W) x t =
        loopStructureMap W x t :=
  congrArg (fun f ↦ f x t) (cylinderLoop_eq_loopStructureMap W)

/-- The actual fiber homeomorphism keeps the original source inclusion and constant path. -/
theorem original_fiber_comparison (x : W.Delooping) :
    relativeFiberHomeomorph W (totalTailFiberComparison (AllWeak.nested W) x) =
      HomotopyFiber.basepoint (relativeProjection W) (doubleBasepoint W)
        (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W)) x)
        (relativeProjection_fiberInclusion W x) :=
  congrArg (fun f ↦ f x) (relativeFiberHomeomorph_comparison W)

/-- The original loop map controls every component, as well as all based finite homotopy sets. -/
theorem original_all_degree_weak (x : W.Delooping) (n : ℕ)
    (γ : Path (doubleBasepoint W) (doubleBasepoint W)) :
    (∃ y, Joined (loopStructureMap W y) γ) ∧
    Function.Bijective (homotopyGroupMap (N := Fin n) (loopStructureMap W) (x := x) rfl) :=
  ⟨(loopStructureMap_isWeakHomotopyEquivalence W).component_surjective γ,
    (loopStructureMap_isWeakHomotopyEquivalence W).homotopy_bijective x n⟩

/-- The new equivalence retains the old degree-raising homomorphism on every original element. -/
theorem original_degree_raising_inverse (n : ℕ) (a : W.K n) :
    degreeRaisingEquiv W n a = degreeRaisingMap W n a ∧
    (degreeRaisingEquiv W n).symm (degreeRaisingMap W n a) = a :=
  ⟨rfl, (degreeRaisingEquiv W n).symm_apply_apply a⟩

/-- The constructed prespectrum's first nontrivial structure map is exactly the proved one. -/
theorem original_prespectrum_first (M : Model.{u}) :
    IsWeakHomotopyEquivalence ((prespectrum M).structureMap 1) :=
  loopStructureMap_isWeakHomotopyEquivalence M.waldhausen

/-- Original independent category universes use the genuine small-model K-equivalence. -/
def original_universe_K_comparison {D : Type u} [Category.{v} D] (V : Structure D) (n : ℕ) :
    V.K n ≃* HomotopyGroup.Pi (n+2) (doubleDelooping V.smallModel) (doubleBasepoint V.smallModel) :=
  (V.smallModelKEquiv n).trans (degreeRaisingEquiv V.smallModel n)

end QuillenTest.IteratedSLoopEquivalence
