/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorUnitNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSchemeLaurentTrack
public import Quillen.KTheory.Bass.SchemeCurrentStageSquare

/-!
# Whole normalized tensor tracks and their actual finite Bass propagation

Realize the genuine tensor-unitor conjugate lifted through original evaluation. Its equality
with the original whole Laurent track transports the existing cone/loop stage constructors.
This identifies the restricted unit action, without asserting a full K-theory product theorem.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalTensorNormalizedTrack
open GlobalSectionChangeIndex GeometricSeedCospan NaturalTrack

/-- Realize the actual globally lifted tensor-unitor normalized automorphism. -/
def homotopy (X : Scheme.{u}ᵒᵖ) :
    Homotopy (GlobalSchemeLaurentTrack.diagram.map (coefficient.app X))
      (GlobalSchemeLaurentTrack.diagram.map (coefficient.app X)) :=
  prespectrumIsoHomotopy (globalModel.map (coefficient.app X))
    (onFunctor (globalModel.map (coefficient.app X)).functor
      (globalNormalizedTensorUnit (laurent.op.obj X) (GlobalSchemeLaurentTrack.laurentScalar X)))

/-- Equality of entire realization homotopies, retaining every original time and level. -/
theorem homotopy_eq (X : Scheme.{u}ᵒᵖ) :
    homotopy X = GlobalSchemeLaurentTrack.homotopy X := by
  unfold homotopy
  rw [globalNormalizedTensorUnit_eq]
  rfl

/-- Actual scheme naturality of the normalized genuine tensor track at the same time. -/
theorem homotopy_naturality {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) (n : ℕ)
    (r : unitInterval) (x : (GlobalSchemeLaurentTrack.diagram.obj X).space n) :
    (GlobalSchemeLaurentTrack.diagram.map (laurent.op.map f)).map n
        ((homotopy X).level n (r, x)) =
      (homotopy Y).level n (r, (GlobalSchemeLaurentTrack.diagram.map f).map n x) := by
  rw [homotopy_eq, homotopy_eq]
  exact GlobalSchemeLaurentTrack.homotopy_naturality f n r x

/-- The original scalar whole track, packaged without changing its homotopy. -/
def scalarTrack : Track laurent.op coefficient GlobalSchemeLaurentTrack.diagram where
  homotopy := GlobalSchemeLaurentTrack.homotopy
  naturality := GlobalSchemeLaurentTrack.homotopy_naturality

/-- The genuine tensor normalization supplies the whole natural track directly. -/
def tensorTrack : Track laurent.op coefficient GlobalSchemeLaurentTrack.diagram where
  homotopy := homotopy
  naturality := homotopy_naturality

/-- The two actual whole tracks agree, including the unchanged coefficient map. -/
theorem tensorTrack_eq : tensorTrack = scalarTrack := by
  have h : homotopy = GlobalSchemeLaurentTrack.homotopy := funext homotopy_eq
  unfold tensorTrack scalarTrack
  congr

/-- Every finite Bass stage retains exactly the existing cone/loop induced unit action. -/
theorem stageTrack_eq (i : ℕ) :
    SchemeNaturalSeed.stageTrack tensorTrack i = SchemeNaturalSeed.stageTrack scalarTrack i := by
  rw [tensorTrack_eq]

/-- The current-stage seed transitions keep their original whole source-null construction. -/
theorem currentTransition_eq (i : ℕ) :
    SchemeNaturalSeed.currentTransition tensorTrack i =
      SchemeNaturalSeed.currentTransition scalarTrack i := by
  rw [tensorTrack_eq]

end Quillen.PerfectComplexes.GlobalTensorNormalizedTrack
