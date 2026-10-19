/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorNormalizedTrack
public import Quillen.KTheory.Bass.ModelZigzagSequentialization
public import Quillen.Topology.Prespectrum.ZigzagSequentializationColimit

/-!
# The actual ordinary-colimit normalized tensor presentation

Original finite Bass vertices and suspension units form a genuine pushout sequentialization.
The forward legs use the normalized genuine tensor track. Its whole equality with the original
current track supplies the factorization, and the original Model topology proves stability of
the comparison to the ordinary colimit. Standard cup-product qualification is separate.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalTensorNormalizedPresentation
open GlobalSectionChangeIndex GlobalTensorNormalizedTrack GeometricSeedCospan
open ModelZigzagSequentialization

/-- The original finite Bass vertex at the actual scheme. -/
abbrev E (X : Scheme.{u}ᵒᵖ) (i : ℕ) := vertex squareFunctor globalModel X i

/-- The literal suspension-loop target of the next original vertex. -/
abbrev V (X : Scheme.{u}ᵒᵖ) (i : ℕ) := suspendedVertex squareFunctor globalModel X i

/-- The actual backward suspension-unit leg. -/
abbrev b (X : Scheme.{u}ᵒᵖ) (i : ℕ) := unit squareFunctor globalModel X i

/-- The original current-stage transition, before sequentialization. -/
def current (X : Scheme.{u}ᵒᵖ) (i : ℕ) : E X i ⟶ E X (i + 1) :=
  (SchemeNaturalSeed.currentTransition scalarTrack i).app X

/-- The forward leg uses the normalized genuine tensor stage and the original unit. -/
def a (X : Scheme.{u}ᵒᵖ) (i : ℕ) : E X i ⟶ V X i :=
  (SchemeNaturalSeed.currentTransition tensorTrack i).app X ≫ b X i

/-- Actual whole factorization follows from the proved normalized-tensor track identity. -/
theorem forward_factorization (X : Scheme.{u}ᵒᵖ) (i : ℕ) :
    a X i = current X i ≫ b X i := by
  unfold a current
  rw [currentTransition_eq]
  rfl

/-- The unchanged whole constant factorization track, with the actual equality transport. -/
def factorization (X : Scheme.{u}ᵒᵖ) (i : ℕ) :
    Quillen.LoopPrespectrum.Homotopy (a X i) (current X i ≫ b X i) :=
  (Quillen.LoopPrespectrum.Homotopy.refl (a X i)).cast rfl (forward_factorization X i)

/-- The prescribed pushout stages, not the current Bass vertices renamed. -/
def stage (X : Scheme.{u}ᵒᵖ) := ZigzagSequentialization.stage (E X) (V X) (a X) (b X)

/-- The actual ordinary colimit of the original pushout sequentialization. -/
def normalizedTensorPresentation (X : Scheme.{u}ᵒᵖ) : LoopPrespectrum.{u+1} :=
  ZigzagSequentialization.ordinaryColimit (E X) (V X) (a X) (b X)

/-- The actual current telescope enters the pushout sequence and then its ordinary colimit. -/
def comparison (X : Scheme.{u}ᵒᵖ) :
    Telescope.prespectrum (E X) (current X) ⟶ normalizedTensorPresentation X :=
  ZigzagSequentialization.telescopeMap (E X) (V X) (a X) (b X)
    (current X) (factorization X) ≫
      ZigzagSequentialization.telescopeToOrdinaryColimit (E X) (V X) (a X) (b X)

/-- Original finite Model topology discharges all stability assumptions of this actual map. -/
theorem comparison_stable (X : Scheme.{u}ᵒᵖ) : IsStableEquivalence (comparison X) := by
  let : ∀ i n, T1Space ((E X i).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space squareFunctor i globalModel X n
  let : ∀ i n, T1Space ((V X i).space n) :=
    fun i n => ModelDiagramSuspension.spaceT1Space squareFunctor (i + 1) globalModel X n
  exact (ModelZigzagSequentialization.telescopeMap_isStableEquivalence
    squareFunctor globalModel X (a X) (current X) (factorization X)).comp
    (ZigzagSequentialization.telescopeToOrdinaryColimit_isStableEquivalence
      (E X) (V X) (a X) (b X))

end Quillen.PerfectComplexes.GlobalTensorNormalizedPresentation
