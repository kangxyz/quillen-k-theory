/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.UniverseLift
public import Quillen.Topology.LocalCoefficients.ComponentComparison

/-! # The original arbitrary-universe chain map on a common-universe space model

The space lift is explicit and independent of the
coefficient-only comparison. Every large target system is pulled back to the
original target before the original certificate is consumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Simplicial
universe u v w
namespace Quillen.LocalCoefficients.CommonUniverseChains

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The unchanged map, conjugated by projection homeomorphisms to a stated common universe. -/
def liftMap (f : C(X, Y)) :
    C(ULift.{max u v w} X, ULift.{max u v w} Y) :=
  UniverseLift.map.{u, v, max u v w} f

@[simp] theorem liftMap_apply (f : C(X, Y)) (x : ULift.{max u v w} X) :
    liftMap.{u, v, w} f x = ULift.up (f x.down) := rfl

/-- Pulling a common-universe system back to the original target and then
performing the original UniverseLift construction has a genuine coefficient inverse. -/
def coefficientRetractIso
    (B : System.{max u v w, max u v w} (ULift.{max u v w} Y)) :
    UniverseLift.system.{v, max u v w, u}
        (pullback (UniverseLift.up.{v, max u v w} Y) B) ≅ B :=
  NatIso.ofComponents (fun x ↦ ULift.moduleEquiv.toModuleIso) (by
    intro x y p
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
    ext a
    rfl)

/-- The coefficient inverse retains the original endpoint and actual coefficient. -/
@[simp] theorem coefficientRetractIso_apply
    (B : System.{max u v w, max u v w} (ULift.{max u v w} Y))
    (y : ULift.{max u v w} Y)
    (a : fiber (UniverseLift.system.{v, max u v w, u}
      (pullback (UniverseLift.up.{v, max u v w} Y) B)) y) :
    (coefficientRetractIso B).hom.app (FundamentalGroupoid.mk y) a = a.down := rfl

/-- The coefficient retract commutes with the actual path and its two specified endpoints. -/
theorem coefficientRetract_transport
    (B : System.{max u v w, max u v w} (ULift.{max u v w} Y))
    {y₀ y₁ : ULift.{max u v w} Y} (p : Path y₀ y₁)
    (a : fiber (UniverseLift.system.{v, max u v w, u}
      (pullback (UniverseLift.up.{v, max u v w} Y) B)) y₀) :
    (transport (UniverseLift.system.{v, max u v w, u}
      (pullback (UniverseLift.up.{v, max u v w} Y) B)) p a).down =
        transport B p a.down := by
  rfl

/-- The source-space lift is compatible with every original singular generator. -/
@[reassoc]
theorem original_chainMap_inclusion (f : C(X, Y))
    (A : System.{v, max u v w} Y) {n : ℕ}
    (σ : SingularSimplex (ULift.{max u v w} X) ⦋n⦌) :
    chainInclusion (UniverseLift.system.{u, max u v w, v} (pullback f A)) σ ≫
        (UniverseLift.chainMap.{u, v, max u v w} f A).f n =
      chainInclusion (UniverseLift.system.{v, max u v w, u} A)
        ((liftMap.{u, v, w} f).comp σ) :=
  UniverseLift.chainInclusion_chainMap f A σ

/-- The full original chain map commutes with the displayed coefficient retract. -/
@[reassoc]
theorem original_chainMap_retract_square (f : C(X, Y))
    (B : System.{max u v w, max u v w} (ULift.{max u v w} Y)) :
    UniverseLift.chainMap.{u, v, max u v w} f
        (pullback (UniverseLift.up.{v, max u v w} Y) B) ≫
      coefficientChainMap (coefficientRetractIso B).hom =
    (coefficientChainIso (UniverseLift.pullbackIso f
      (pullback (UniverseLift.up.{v, max u v w} Y) B))).hom ≫
        coefficientChainMap (pullbackMap (liftMap.{u, v, w} f)
          (coefficientRetractIso B).hom) ≫
        pushforwardChainMap (liftMap.{u, v, w} f) B := by
  rw [UniverseLift.chainMap, Category.assoc,
    ← pushforwardChainMap_coefficient_naturality]
  rfl

/-- A certificate on the original map supplies all same-universe systems on its
explicit common-universe model; no large system is assumed to be small. -/
theorem all_localCoefficients_liftMap (f : C(X, Y))
    (h : ∀ A : System.{v, max u v w} Y,
      QuasiIso (UniverseLift.chainMap.{u, v, max u v w} f A)) :
    ∀ B : System.{max u v w, max u v w} (ULift.{max u v w} Y),
      QuasiIso (UniverseLift.chainMap.{max u v w, max u v w, max u v w}
        (liftMap.{u, v, w} f) B) := by
  intro B
  let A := pullback (UniverseLift.up.{v, max u v w} Y) B
  have hA := h A
  have hspatial : QuasiIso (pushforwardChainMap (liftMap.{u, v, w} f)
      (UniverseLift.system.{v, max u v w, u} A)) := by
    let : QuasiIso ((coefficientChainIso (UniverseLift.pullbackIso f A)).hom ≫
        pushforwardChainMap (liftMap.{u, v, w} f)
          (UniverseLift.system.{v, max u v w, u} A)) := hA
    exact quasiIso_of_comp_left (coefficientChainIso (UniverseLift.pullbackIso f A)).hom _
  have hB := pushforwardChainMap_quasiIso_of_coefficientIso (liftMap.{u, v, w} f)
    (coefficientRetractIso B) hspatial
  rw [← quasiIso_iff_comp_right _ (UniverseLift.chainComparisonIso B).hom,
    UniverseLift.chainComparisonIso_naturality, quasiIso_iff_comp_left]
  exact hB


end Quillen.LocalCoefficients.CommonUniverseChains
