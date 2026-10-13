/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.CoveringHomologyComparison

/-! Actual path-basis, equality-cast, coefficient-inverse, and covering-scope tests. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LocalCoefficients
universe u v

namespace QuillenTest.CoverCoefficientTransport

open Quillen
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- One displayed connecting path suffices even without source connectivity. -/
theorem onePath (f : C(X, Y)) (b x : X) (p : Path b x)
    (hf : Function.Bijective (FundamentalGroup.map f b)) :
    Function.Bijective (fun q : Path.Homotopic.Quotient b x ↦ q.map f) :=
  pathClassMap_bijective_of_fundamentalGroupMap f b x p hf

/-- Every equivalence image is the original path-class image, across universes. -/
theorem originalPathImage [PathConnectedSpace X] (f : C(X, Y)) (b x : X)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl))
    (q : Path.Homotopic.Quotient b x) : pathClassMapEquiv f b x hf q = q.map f := rfl

/-- Identity Pi one transport supplies the hypothesis with no assumed coefficient inverse. -/
theorem identityCoefficient [PathConnectedSpace X] (b : X) :
    IsIso (regularMap (ContinuousMap.id X) b) := by
  apply regularMap_isIso
  rw [piMap, homotopyGroupMapHom_id]
  exact ⟨fun _ _ hab ↦ hab, fun a ↦ ⟨a, rfl⟩⟩

variable {Z : Type u} [TopologicalSpace Z] [PathConnectedSpace X]

/-- The forward coefficient isomorphism still maps each original path basis element. -/
theorem originalRegularGenerator (f : C(X, Z)) (b x : X)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl))
    (q : Path.Homotopic.Quotient b x) (a : ℤ) :
    (regularCoefficientIso f b (f b) rfl hf).hom.app (FundamentalGroupoid.mk x)
      (regularSingle b q a) = regularSingle (f b) (q.map f) a := by
  simpa only [regularCoefficientIso_hom, regularMapTo, eqToHom_refl,
    Category.comp_id] using regularMap_single f b q a

/-- An arbitrary displayed equality at the basepoint remains in the exact chain map. -/
theorem exactCoefficientForward (f : C(X, Z)) (b : X) (b' : Z) (hb : b' = f b)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl)) :
    (regularCoefficientChainIso f b b' hb hf).hom =
      coefficientChainMap (regularMapTo f b b' hb) := rfl

/-- The new inverse cancels the actual original coefficient chain map on both sides. -/
theorem genuineChainInverse (f : C(X, Z)) (b : X) (b' : Z) (hb : b' = f b)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl)) :
    coefficientChainMap (regularMapTo f b b' hb) ≫
        (regularCoefficientChainIso f b b' hb hf).inv = 𝟙 _ ∧
      (regularCoefficientChainIso f b b' hb hf).inv ≫
        coefficientChainMap (regularMapTo f b b' hb) = 𝟙 _ :=
  ⟨(regularCoefficientChainIso f b b' hb hf).hom_inv_id,
    (regularCoefficientChainIso f b b' hb hf).inv_hom_id⟩

/-- A supplied covering map can miss a component even when its total space is a point. -/
theorem coveringNeedNotSurject :
    IsCoveringMap (fun _ : PUnit ↦ (false : Bool)) ∧
      ¬ Function.Surjective (fun _ : PUnit ↦ (false : Bool)) := by
  refine ⟨IsCoveringMap.of_discreteTopology _, ?_⟩
  intro h
  obtain ⟨x, hx⟩ := h true
  exact Bool.false_ne_true hx

end QuillenTest.CoverCoefficientTransport
