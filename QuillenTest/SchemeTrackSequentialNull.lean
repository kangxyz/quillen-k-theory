/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeTrackSequentialNull

/-! Original-clock and literal-endpoint regressions for the actual same-null consumer. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped unitInterval
universe u w
namespace QuillenTest.SchemeTrackSequentialNull
open Quillen.KTheory.Bass Quillen.KTheory.Bass.NaturalTrack
open Quillen.KTheory.Bass.GeometricSeedCospan
open Quillen.KTheory.Bass.ModelZigzagSequentialization
open Quillen.KTheory.Bass.SchemeTrackSequentialPresentation

/-- Original family time and the actual suspension-unit loop time remain independent. -/
theorem original_unit_clock {E F : Quillen.LoopPrespectrum.{w}} {f g : E ⟶ F}
    (H : Homotopy f g) (n : ℕ) (r s : unitInterval) (x : E.space n) :
    Path.toContinuousMap (H.suspensionLoop.level n
      (r, (suspensionLoopUnit E).map n x)) s =
        Quillen.ReducedMappingCone.cylinder (F.point n) (pointPrespectrum.point n)
          ((Quillen.LoopPrespectrum.zeroHom F pointPrespectrum).map n) (s, H.level n (r, x)) := rfl

variable (M₀ M₁ M₂ : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (A₀ : Track laurent.op coefficient (M₀ ⋙ prespectrumFunctor))
    (A₁ : Track laurent.op coefficient (M₁ ⋙ prespectrumFunctor))
    (A₂ : Track laurent.op coefficient (M₂ ⋙ prespectrumFunctor))
    (X₀ X₁ X₂ : Scheme.{u}ᵒᵖ)
    (d : ∀ i, vertex squareFunctor M₀ X₀ i ⟶ vertex squareFunctor M₁ X₁ i)
    (e : ∀ i, vertex squareFunctor M₁ X₁ i ⟶ vertex squareFunctor M₂ X₂ i)
    (hd : ∀ i, current M₀ A₀ X₀ i ≫ d (i + 1) = d i ≫ current M₁ A₁ X₁ i)
    (he : ∀ i, current M₁ A₁ X₁ i ≫ e (i + 1) = e i ≫ current M₂ A₂ X₂ i)
    (N : ∀ i, Homotopy (d i ≫ e i)
      (Quillen.LoopPrespectrum.zeroHom
        (vertex squareFunctor M₀ X₀ i) (vertex squareFunctor M₂ X₂ i)))
    (hN : ∀ i n r x, (current M₂ A₂ X₂ i).map n ((N i).level n (r, x)) =
      (N (i + 1)).level n (r, (current M₀ A₀ X₀ i).map n x))

/-- The given original finite null retains its null time and original telescope height. -/
theorem original_null_clock (i n : ℕ) (r s : unitInterval)
    (x : (vertex squareFunctor M₀ X₀ i).space n) :
    (originalCurrentNull M₀ M₁ M₂ A₀ A₁ A₂ X₀ X₁ X₂ d e hd he N hN).level n
        (r, Telescope.cylinder (vertex squareFunctor M₀ X₀) (current M₀ A₀ X₀) n i (s, x)) =
      Telescope.cylinder (vertex squareFunctor M₂ X₂) (current M₂ A₂ X₂) n i
        (s, (N i).level n (r, x)) := rfl

/-- The actual ordinary composite null ends at the literal original target point. -/
theorem ordinary_literal_endpoint (n : ℕ) (q : (presentation M₀ A₀ X₀).space n) :
    (ordinaryCompositeNull M₀ M₁ M₂ A₀ A₁ A₂ X₀ X₁ X₂ d e hd he N hN).level n (1, q) =
      (presentation M₂ A₂ X₂).point n :=
  (ordinaryCompositeNull M₀ M₁ M₂ A₀ A₁ A₂ X₀ X₁ X₂ d e hd he N hN).at_one n q

end QuillenTest.SchemeTrackSequentialNull
