/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SectionChangeIndexMixedModel
public import Quillen.KTheory.Bass.ModelDiagramStableEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSections

/-!
# Original global bounded-flat sections and coefficient restriction

The global geometric pseudofunctor, its original Waldhausen structures and their chosen zeros
supply the section construction. Restriction uses the actual coefficient base-product functor.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.Waldhausen.IteratedS.SectionChangeIndexMixedModel
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The original geometric Waldhausen structures on all scheme fibers. -/
def fiberWaldhausen (X : Scheme.{u}ᵒᵖ) :
    Waldhausen.Structure (boundedFlatPerfectPseudofunctor.obj ⟨X⟩) :=
  boundedFlatPerfectWaldhausen X.unop

/-- One original zero family on all scheme fibers. -/
def fiberZero (X : Scheme.{u}ᵒᵖ) : boundedFlatPerfectPseudofunctor.obj ⟨X⟩ :=
  (fiberWaldhausen X).zero

/-- Every selected global fiber zero is zero. -/
theorem fiberZero_isZero (X : Scheme.{u}ᵒᵖ) : IsZero (fiberZero X) :=
  (fiberWaldhausen X).isZero

/-- Actual geometric transition preserves the global zero family up to being zero. -/
theorem fiberZero_map_isZero {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    IsZero ((boundedFlatPerfectPseudofunctor.map f.toLoc).toFunctor.obj (fiberZero X)) :=
  (boundedFlatPerfectPullback f.unop).map_isZero (fiberZero_isZero X)

/-- Original geometric pullback is exact for the original fiber structures. -/
theorem fiber_exact {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    Waldhausen.IsExact (fiberWaldhausen X).cof (fiberWaldhausen X).weq
      (fiberWaldhausen Y).cof (fiberWaldhausen Y).weq
      (boundedFlatPerfectPseudofunctor.map f.toLoc).toFunctor :=
  boundedFlatPerfectPullback_exact f.unop

/-- The actual global strict Model diagram of bounded-flat cocartesian sections. -/
def globalModel : Scheme.{u}ᵒᵖ ⥤ Model.{u+1} :=
  modelDiagram boundedFlatPerfectPseudofunctor fiberWaldhausen fiberZero
    fiberZero_isZero (fun {_ _} f => fiberZero_map_isZero f)
    (fun {_ _} f => fiber_exact f)

/-- Restriction lands in the existing coefficient-first Model diagram, with its original zero. -/
def coefficientRestriction (R : CommRingCat.{u}) :
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R ⋙ globalModel ⟶
      boundedFlatCoefficientSectionModelFunctor R :=
  restrictionModel boundedFlatPerfectPseudofunctor fiberWaldhausen fiberZero
    fiberZero_isZero (fun {_ _} f => fiberZero_map_isZero f)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R)
    (fun {_ _} f => fiber_exact f)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
