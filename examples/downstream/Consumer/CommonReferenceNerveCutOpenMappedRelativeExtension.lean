/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenMappedRelativeExtension

/-! Exact route recovery and independent parameters after the actual native cone map. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open CommonReferenceNerve.CutOpenCarrier
open scoped Topology unitInterval
universe u
namespace Consumer.CommonReferenceNerveCutOpenMappedRelativeExtension
variable {V W T : Model.{u}} {F : V ⟶ W} {J : W ⟶ T} {G : V ⟶ T}
  {ε₀ ε₁ : G.functor ≅ (F ≫ J).functor}
  (B : RelativeBoundary F J G ε₀ ε₁)
  {P : LoopPrespectrum.{u}} (j : nativeCone J ⟶ P)
  {f g : prespectrum V ⟶ parameterLooping P} (H K : Homotopy f g)
  (h : B.RecoversMappedRoutes j H K)

/-- The client supplies only the six carrier faces and their actual two mapped route identities. -/
def comparison (h : B.RecoversMappedRoutes j H K) : H.RelHomotopy K :=
  B.mappedRelativeComparison j H K h

/-- The client retains every seed value on the original route. -/
theorem original_route (n : ℕ) (s t : I) (x : (prespectrum V).space n) :
    Path.toContinuousMap ((comparison B j H K h).level n (0, (s, x))) t =
      Path.toContinuousMap (H.level n (s, x)) t :=
  congrArg (fun p ↦ Path.toContinuousMap p t)
    (((comparison B j H K h).level n).apply_zero (s, x))

end Consumer.CommonReferenceNerveCutOpenMappedRelativeExtension
