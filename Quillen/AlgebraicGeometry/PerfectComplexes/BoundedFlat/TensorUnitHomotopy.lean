/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnit
public import Quillen.Waldhausen.SConstruction.Iterated.ExactPastingHomotopy

/-!
# Original iterated-S tracks of the restricted tensor-unit action

Tensoring by the actual structure module is exact through its genuine unitor. The actual
coefficient-unit automorphism therefore supplies an original iterated-S track. Its categorical
unitor square gives a whole relative prism comparison with the existing forward scalar track,
including the original zero-level loops and independent spectrum structure parameter.

This is the restricted tensor-unit comparison. No full K-theory product or identification of
arbitrary Bass towers with the classical TT construction is asserted here.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- Genuine tensor by the structure module preserves zero, cofibrations, weak equivalences and
pushouts through the actual left unitor. -/
theorem boundedFlatPerfectTensorUnit_exact (X : Scheme.{u}) :
    Waldhausen.IsExact (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq (boundedFlatPerfectTensorUnit X) :=
  (Waldhausen.IsExact.id _ _).of_iso (boundedFlatPerfectTensorUnitIso X).symm

/-- The actual tensor-unit pullback, with no flatness hypothesis on the scheme map, is exact. -/
theorem boundedFlatPerfectTensorUnitPullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Waldhausen.IsExact (boundedFlatPerfectWaldhausen Y).cof
      (boundedFlatPerfectWaldhausen Y).weq (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq (boundedFlatPerfectTensorUnitPullback f) :=
  (boundedFlatPerfectPullback_exact f).of_iso (boundedFlatPerfectTensorUnitPullbackIso f).symm

/-- The original tensor automorphism fixes the actual zero input before canonical rebasing. -/
theorem boundedFlatPerfectTensorUnitPullbackAutomorphism_zero {X Y : Scheme.{u}}
    (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom.app
        (boundedFlatPerfectWaldhausen Y).zero = 𝟙 _ :=
  ((boundedFlatPerfectTensorUnitPullback_exact f).zero
    (boundedFlatPerfectWaldhausen Y).isZero).eq_of_src _ _

/-- The normalized original spectrum map of genuine tensor-unit geometric pullback. -/
def boundedFlatPerfectTensorUnitPrespectrumMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectTensorUnitPullback_exact f)

/-- The whole iterated-S track of the actual tensor coefficient automorphism. -/
def boundedFlatPerfectTensorUnitHomotopy {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    Homotopy (boundedFlatPerfectTensorUnitPrespectrumMap f)
      (boundedFlatPerfectTensorUnitPrespectrumMap f) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (boundedFlatPerfectTensorUnitPullback_exact f)
    (boundedFlatPerfectTensorUnitPullback_exact f)
    (boundedFlatPerfectTensorUnitPullbackAutomorphism f r)

/-- The original unitor supplies a full spectrum homotopy to unchanged geometric pullback. -/
def boundedFlatPerfectTensorUnitUnitorHomotopy {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy (boundedFlatPerfectTensorUnitPrespectrumMap f)
      (boundedFlatPerfectPrespectrumMap f) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (boundedFlatPerfectTensorUnitPullback_exact f)
    (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectTensorUnitPullbackIso f)

/-- The actual tensor-unit square realizes to the whole endpoint-relative iterated-S prism.
Both original times and the independent structure coordinate are retained. -/
def boundedFlatPerfectTensorUnitUnitorPasting {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    ((boundedFlatPerfectTensorUnitHomotopy f r).trans
      (boundedFlatPerfectTensorUnitUnitorHomotopy f)).RelHomotopy
      ((boundedFlatPerfectTensorUnitUnitorHomotopy f).trans
        (boundedFlatPerfectUnitHomotopy f r)) :=
  exactOriginalPrespectrumPastingHomotopy _ _
    (boundedFlatPerfectTensorUnitPullback_exact f) (boundedFlatPerfectTensorUnitPullback_exact f)
    (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectPullback_exact f)
    (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom
    (boundedFlatPerfectTensorUnitPullbackIso f).hom
    (boundedFlatPerfectTensorUnitPullbackIso f).hom
    (boundedFlatPerfectPullbackUnitIso f r).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (boundedFlatPerfectTensorUnitPullbackAutomorphism_unitor f r)

end Quillen.PerfectComplexes
