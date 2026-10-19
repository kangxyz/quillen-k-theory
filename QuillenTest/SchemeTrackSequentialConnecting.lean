/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeTrackSequentialDiagramNull
public import Quillen.Topology.Prespectrum.FiberLiftConnecting

/-!
# All-signed intrinsic connecting regression for the actual same-null presentation

The target connecting map is the existing intrinsic connecting map of the ordinary pair
and its specified original null. It is not defined by conjugating the source boundary.
No Bass-class or sign identification beyond the original signed fiber API is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u w
namespace QuillenTest.SchemeTrackSequentialConnecting
open Quillen.KTheory.Bass Quillen.KTheory.Bass.NaturalTrack
open Quillen.KTheory.Bass.GeometricSeedCospan
open Quillen.KTheory.Bass.SchemeNaturalSeed
open Quillen.KTheory.Bass.SchemeTrackSequentialPresentation
variable (M₀ M₁ M₂ : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (A₀ : Track laurent.op coefficient (M₀ ⋙ prespectrumFunctor))
    (A₁ : Track laurent.op coefficient (M₁ ⋙ prespectrumFunctor))
    (A₂ : Track laurent.op coefficient (M₂ ⋙ prespectrumFunctor))
    (η : M₀ ⋙ prespectrumFunctor ⟶ M₁ ⋙ prespectrumFunctor) (hη : Equivariant A₀ A₁ η)
    (θ : M₁ ⋙ prespectrumFunctor ⟶ M₂ ⋙ prespectrumFunctor) (hθ : Equivariant A₁ A₂ θ)
    (N : DiagramNullHomotopy η θ)
    (hN : ∀ r, Equivariant A₀ A₂
      (diagramHomotopyAt (η := η ≫ θ)
        (θ := diagramZeroMap (M₀ ⋙ prespectrumFunctor) (M₂ ⋙ prespectrumFunctor))
        N.homotopy N.naturality r))
    (X : Scheme.{u}ᵒᵖ)
    (hcur : IsStableEquivalence (homotopyFiberLift ((currentInputMap A₁ A₂ θ hθ).app X)
      ((currentInputMap A₀ A₁ η hη).app X)
      ((currentInputNull A₀ A₁ A₂ η θ hη hθ N hN).homotopy X)))

/-- Every signed degree preserves the connecting maps intrinsic to the two specified nulls. -/
theorem signed_connecting_square (d : ℤ) :
    letI := hcur d
    letI := ((currentInputLift_stable_iff M₀ M₁ A₀ A₁ η hη M₂ A₂ θ hθ N hN X).mp hcur) d
    stableFiberLiftConnecting ((currentInputMap A₀ A₁ η hη).app X)
        ((currentInputMap A₁ A₂ θ hθ).app X)
        ((currentInputNull A₀ A₁ A₂ η θ hη hθ N hN).homotopy X) d ≫
      (stableHomotopyFunctor d).map (comparison M₀ A₀ X) =
    (stableHomotopyFunctor (d + 1)).map (comparison M₂ A₂ X) ≫
      stableFiberLiftConnecting ((ordinaryInputMap M₀ M₁ A₀ A₁ η hη).app X)
        ((ordinaryInputMap M₁ M₂ A₁ A₂ θ hθ).app X)
        ((ordinaryInputNull M₀ M₁ A₀ A₁ η hη M₂ A₂ θ hθ N hN).homotopy X) d := by
  let := hcur d
  let := ((currentInputLift_stable_iff M₀ M₁ A₀ A₁ η hη M₂ A₂ θ hθ N hN X).mp hcur) d
  exact stableFiberLiftConnecting_naturality _ _ _ _ _ _
    (comparison M₀ A₀ X) (comparison M₁ A₁ X) (comparison M₂ A₂ X)
    (congrArg (fun t ↦ t.app X) (ordinaryInputMap_comparison M₀ M₁ A₀ A₁ η hη))
    (congrArg (fun t ↦ t.app X) (ordinaryInputMap_comparison M₁ M₂ A₁ A₂ θ hθ)).symm
    (ordinaryInputNull_comparison M₀ M₁ A₀ A₁ η hη M₂ A₂ θ hθ N hN X) d

end QuillenTest.SchemeTrackSequentialConnecting
