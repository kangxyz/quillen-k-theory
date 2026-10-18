/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenPairDiagram
public import Quillen.Aglib.AlgebraicGeometry.Products.IntegerBaseCoefficientRow

/-! # The original projection identifies the integer parameter basepoint Models -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterIdentity

/-- The actual fixed-factor projection at the identity integer parameter. -/
def projectionIso (Q : Scheme.{u}) :
    (baseProductFunctor (toIntegerBase Q)).obj integerBase ≅ Q :=
  IntegerRow.identityIso (Over.mk (toIntegerBase Q))

/-- This is the original projection, not an independently selected scheme equivalence. -/
theorem projectionIso_hom (Q : Scheme.{u}) :
    (projectionIso Q).hom = pullback.snd _ _ :=
  IntegerRow.identityIso_hom (Over.mk (toIntegerBase Q))

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original open immersion as an actual open pair. -/
def originalPair : Scheme.OpenPairs.{u} :=
  ⟨Arrow.mk f, by change IsOpenImmersion f; infer_instance⟩

/-- The two original projections give the complete basepoint open-pair isomorphism. -/
def projectionPairIso : GlobalSupportedParameter.pair f integerBase ≅ originalPair f :=
  Scheme.openPairProperty.isoMk (Arrow.isoMk (projectionIso P) (projectionIso Q) (by
    change (projectionIso P).hom ≫ f =
      (GlobalSupportedParameter.openTransformation f).app integerBase ≫ (projectionIso Q).hom
    rw [projectionIso_hom, projectionIso_hom]
    dsimp only [GlobalSupportedParameter.openTransformation, baseProductTransformation]
    exact (pullback.lift_snd _ _ _).symm))

/-- Contravariant pullback along the original projection identifies the ambient Models. -/
def ambientIso (Q : Scheme.{u}) :
    globalModel.obj (op Q) ≅ (ParameterModels.ambient Q).obj (op integerBase) :=
  globalModel.mapIso (projectionIso Q).op

/-- The same actual pair projection identifies the original supported Models and zeros. -/
def supportedIso : supportedModel (X := op Q) f ≅
    (ParameterModels.supported f).obj (op integerBase) :=
  pairSupported.mapIso (projectionPairIso f).op

/-- Forgetting the original support commutes with the actual projection identification. -/
theorem supportedIso_forget :
    (supportedIso f).hom ≫ (ParameterModels.forget f).app (op integerBase) =
      supportedForget (X := op Q) f ≫ (ambientIso Q).hom :=
  (pairForget.naturality (projectionPairIso f).hom.op).symm

/-- The actual full-open restriction commutes with the same projection identification. -/
theorem ambientIso_fullRestriction :
    (ambientIso Q).hom ≫
        ((ParameterModels.changeWeak f).app (op integerBase) ≫
          (ParameterModels.openRestriction f).app (op integerBase)) =
      globalModel.map f.op ≫ (ambientIso P).hom := by
  have h := pairRestriction.naturality (projectionPairIso f).hom.op
  have hf := congrArg (fun η => η.app (op (GlobalSupportedParameter.pair f integerBase)))
    pairOpen_factor
  exact (congrArg (fun k => (ambientIso Q).hom ≫ k) hf).trans h

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterIdentity
