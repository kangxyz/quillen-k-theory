/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitHomotopy
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSchemeLaurentTrack

/-!
# The original forward Laurent coordinate in the restricted tensor-unit prism

The coordinate is the existing unit pulled back by the actual second product projection.
Original global evaluation identifies its section action with the genuine coefficient tensor
action through the actual unitor. The original geometric Laurent projection also has the whole
restricted tensor-unit prism, with the forward coordinate and all normalization data unchanged.

This supplies a finite action comparison. A classical tensor-pairing presentation and the
TT loop-suspension/homotopy-colimit comparison remain separate mathematical obligations.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.GlobalSchemeLaurentTrack
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- Actual evaluation sees the original forward Laurent unit as genuine coefficient tensor,
through the original left unitor, on every section object. -/
theorem globalLaurentUnit_tensor_evaluation (X : Scheme.{u}ᵒᵖ)
    (S : globalModel.obj (laurent.op.obj X)) :
    (boundedFlatPerfectTensorUnitAutomorphism (laurent.op.obj X).unop
        (laurentScalar X)).hom.app ((globalEvaluation (laurent.op.obj X)).obj S) ≫
      (boundedFlatPerfectTensorUnitIso (laurent.op.obj X).unop).hom.app
        ((globalEvaluation (laurent.op.obj X)).obj S) =
    (boundedFlatPerfectTensorUnitIso (laurent.op.obj X).unop).hom.app
        ((globalEvaluation (laurent.op.obj X)).obj S) ≫
      (globalEvaluation (laurent.op.obj X)).map ((GlobalSchemeLaurentTrack.unit X).hom.app S) := by
  rw [GlobalSchemeLaurentTrack.unit, globalUnit_evaluation]
  exact NatTrans.congr_app
    (boundedFlatPerfectTensorUnitAutomorphism_unitor (laurent.op.obj X).unop (laurentScalar X))
    ((globalEvaluation (laurent.op.obj X)).obj S)

/-- The actual Laurent geometric projection and forward coordinate specialize the whole
restricted tensor-unit prism, including the unchanged original spectrum normalization. -/
def globalLaurentTensorUnitPasting (X : Scheme.{u}ᵒᵖ) :
    ((boundedFlatPerfectTensorUnitHomotopy (Quillen.KTheory.Bass.GeometricSeedCospan.coefficient.app
        X).unop (laurentScalar X)).trans
      (boundedFlatPerfectTensorUnitUnitorHomotopy
        (Quillen.KTheory.Bass.GeometricSeedCospan.coefficient.app X).unop)).RelHomotopy
      ((boundedFlatPerfectTensorUnitUnitorHomotopy
        (Quillen.KTheory.Bass.GeometricSeedCospan.coefficient.app X).unop).trans
          (boundedFlatPerfectUnitHomotopy
            (Quillen.KTheory.Bass.GeometricSeedCospan.coefficient.app X).unop
            (laurentScalar X))) :=
  boundedFlatPerfectTensorUnitUnitorPasting
    (Quillen.KTheory.Bass.GeometricSeedCospan.coefficient.app X).unop (laurentScalar X)

end Quillen.PerfectComplexes
