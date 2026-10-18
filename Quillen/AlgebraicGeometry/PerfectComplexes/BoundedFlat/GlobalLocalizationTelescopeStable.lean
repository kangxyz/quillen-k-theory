/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalLocalizationEquivalence

/-! # Actual supported and coarse global telescope restriction is stable -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

namespace SupportedTelescope

/-- The actual finite restriction is stable by its exact categorical inverse. -/
theorem finiteRestriction_isStableEquivalence (i : ℕ) (a : Under R) :
    IsStableEquivalence ((finiteRestriction f i).app a) :=
  supportedRowRestriction_iterate_isStableEquivalence f (laurentUnderSquareFunctor R) i a

/-- The actual natural telescope restriction is pointwise a stable equivalence. -/
theorem telescopeRestriction_isStableEquivalence (a : Under R) :
    IsStableEquivalence ((telescopeRestriction f).app a) := by
  let : ∀ i n, T1Space (((globalDiagram f i).obj a).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (supportedRow f) a n
  let : ∀ i n, T1Space (((boundedFlatCoefficientSupportedBassDiagram f i).obj a).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedModelFunctor f) a n
  exact Telescope.map_isStableEquivalence
    (fun i => (globalDiagram f i).obj a) (fun i => (globalTransition f i).app a)
    (fun i => (boundedFlatCoefficientSupportedBassDiagram f i).obj a)
    (fun i => (boundedFlatCoefficientSupportedBassTransition f i).app a)
    (fun i => (finiteRestriction f i).app a)
    (fun i => congrArg (fun η => η.app a) (finiteRestriction_transition f i))
    (fun i => finiteRestriction_isStableEquivalence f i a)


end SupportedTelescope

namespace OpenTelescope

/-- The actual finite restriction is stable by its exact categorical inverse. -/
theorem finiteRestriction_isStableEquivalence (i : ℕ) (a : Under R) :
    IsStableEquivalence ((finiteRestriction f i).app a) :=
  openRowRestriction_iterate_isStableEquivalence f (laurentUnderSquareFunctor R) i a

/-- The actual natural telescope restriction is pointwise a stable equivalence. -/
theorem telescopeRestriction_isStableEquivalence (a : Under R) :
    IsStableEquivalence ((telescopeRestriction f).app a) := by
  let : ∀ i n, T1Space (((globalDiagram f i).obj a).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (openRow f) a n
  let : ∀ i n, T1Space (((boundedFlatCoefficientOpenBassDiagram f i).obj a).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientOpenModelFunctor f) a n
  exact Telescope.map_isStableEquivalence
    (fun i => (globalDiagram f i).obj a) (fun i => (globalTransition f i).app a)
    (fun i => (boundedFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i => (boundedFlatCoefficientOpenBassTransition f i).app a)
    (fun i => (finiteRestriction f i).app a)
    (fun i => congrArg (fun η => η.app a) (finiteRestriction_transition f i))
    (fun i => finiteRestriction_isStableEquivalence f i a)


end OpenTelescope

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
