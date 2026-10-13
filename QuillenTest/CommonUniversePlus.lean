/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.CommonUniverse

/-! # Exact chain, endpoint and subgroup tests for the common-universe plus adapter -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Simplicial
universe u v w
namespace QuillenTest.CommonUniversePlus
open Quillen Quillen.LocalCoefficients
open Quillen.LocalCoefficients.CommonUniverseChains
open Quillen.PlusConstruction.CommonUniverse

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual simplex indices commute with every operator, including repeated vertices. -/
theorem all_operator_indices {m n : SimplexCategory}
    (σ : SingularSimplex (ULift.{w} X) n) (α : m ⟶ n) :
    UniverseLift.simplexEquiv X m (restrictSimplex σ α) =
      restrictSimplex (UniverseLift.simplexEquiv X n σ) α :=
  UniverseLift.simplexEquiv_restrict σ α

/-- The original mixed-universe chain map retains each singular generator. -/
theorem original_generator (f : C(X, Y)) (A : System.{v, max u v w} Y) {n : ℕ}
    (σ : SingularSimplex (ULift.{max u v w} X) ⦋n⦌) :
    chainInclusion (UniverseLift.system.{u, max u v w, v} (pullback f A)) σ ≫
        (UniverseLift.chainMap.{u, v, max u v w} f A).f n =
      chainInclusion (UniverseLift.system.{v, max u v w, u} A)
        ((liftMap.{u, v, w} f).comp σ) := original_chainMap_inclusion f A σ

/-- Both endpoints and nontrivial coefficient transport remain the original ones. -/
theorem endpoint_transport
    (B : System.{max u v w, max u v w} (ULift.{max u v w} Y))
    {y₀ y₁ : ULift.{max u v w} Y} (p : Path y₀ y₁)
    (a : fiber (UniverseLift.system.{v, max u v w, u}
      (pullback (UniverseLift.up.{v, max u v w} Y) B)) y₀) :
    (transport (UniverseLift.system.{v, max u v w, u}
      (pullback (UniverseLift.up.{v, max u v w} Y) B)) p a).down =
        transport B p a.down := coefficientRetract_transport B p a

/-- The full chain square concerns the original mixed-universe chain map. -/
theorem original_chain_square (f : C(X, Y))
    (B : System.{max u v w, max u v w} (ULift.{max u v w} Y)) :
    UniverseLift.chainMap.{u, v, max u v w} f
        (pullback (UniverseLift.up.{v, max u v w} Y) B) ≫
      coefficientChainMap (coefficientRetractIso B).hom =
    (coefficientChainIso (UniverseLift.pullbackIso f
      (pullback (UniverseLift.up.{v, max u v w} Y) B))).hom ≫
        coefficientChainMap (pullbackMap (liftMap.{u, v, w} f)
          (coefficientRetractIso B).hom) ≫
        pushforwardChainMap (liftMap.{u, v, w} f) B := original_chainMap_retract_square f B

variable (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y)

/-- Spatial transport is exactly conjugation by the two projection homeomorphisms. -/
theorem original_forward :
    (UniverseLift.down Y).comp
      ((liftMap.{u, v, w} f).comp (UniverseLift.up X)) = f := forward_down f

/-- Projecting the specified lifted path recovers that path exactly. -/
theorem original_track : (liftPath.{u, v, w} f γ).map continuous_uliftDown = γ :=
  liftPath_down f γ

/-- The based nonabelian Pi-one square retains the original under-basepoint track. -/
theorem based_square :
    (basedPiOneMap (liftMap.{u, v, w} f) (liftPath f γ)).comp
        (piEquiv.{u, max u v w} x).toMonoidHom =
      (piEquiv.{v, max u v w} y).toMonoidHom.comp (basedPiOneMap f γ) :=
  basedPiOneMap_square f γ

/-- The precise original kernel is carried by the stated subgroup image. -/
theorem original_kernel :
    (basedPiOneMap (liftMap.{u, v, w} f) (liftPath f γ)).ker =
      liftSubgroup.{u, max u v w} (basedPiOneMap f γ).ker := kernel_lift f γ

end QuillenTest.CommonUniversePlus
