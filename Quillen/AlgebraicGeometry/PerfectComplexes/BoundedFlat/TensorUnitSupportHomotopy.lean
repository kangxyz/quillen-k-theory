/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportComparison
public import Quillen.Waldhausen.SConstruction.Iterated.ExactPastingHomotopy

/-!
# The original supported tensor-unit prism

The inherited Waldhausen structure retains the actual open-restriction acyclicity property.
The tensor-unit unitor square gives a whole relative comparison of original iterated-S tracks
on this supported category, with canonical zero rebasing and the original endpoint maps.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual unit tensor preserves the inherited supported Waldhausen structure. -/
theorem boundedFlatPerfectSupportedTensorUnit_exact :
    Waldhausen.IsExact (boundedFlatPerfectSupportedWaldhausen j).cof
      (boundedFlatPerfectSupportedWaldhausen j).weq
      (boundedFlatPerfectSupportedWaldhausen j).cof
      (boundedFlatPerfectSupportedWaldhausen j).weq (boundedFlatPerfectSupportedTensorUnit j) :=
  (Waldhausen.IsExact.id _ _).of_iso (boundedFlatPerfectSupportedTensorUnitIso j).symm

/-- The original supported tensor automorphism fixes the chosen zero before rebasing. -/
theorem boundedFlatPerfectSupportedTensorUnitAutomorphism_zero (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectSupportedTensorUnitAutomorphism j r).hom.app
        (boundedFlatPerfectSupportedWaldhausen j).zero = 𝟙 _ :=
  ((boundedFlatPerfectSupportedTensorUnit_exact j).zero
    (boundedFlatPerfectSupportedWaldhausen j).isZero).eq_of_src _ _

/-- The normalized original prespectrum map of supported unit tensor. -/
def boundedFlatPerfectSupportedTensorUnitPrespectrumMap :=
  exactOriginalPrespectrumMap (boundedFlatPerfectSupportedWaldhausen j)
    (boundedFlatPerfectSupportedWaldhausen j) (boundedFlatPerfectSupportedTensorUnit_exact j)

/-- The original supported identity functor retains its canonical zero normalization. -/
def boundedFlatPerfectSupportedIdentityPrespectrumMap :=
  exactOriginalPrespectrumMap (boundedFlatPerfectSupportedWaldhausen j)
    (boundedFlatPerfectSupportedWaldhausen j) (Waldhausen.IsExact.id _ _)

/-- The full original iterated-S loop of the supported coefficient tensor action. -/
def boundedFlatPerfectSupportedTensorUnitHomotopy (r : (Γ(X, ⊤))ˣ) :
    Homotopy (boundedFlatPerfectSupportedTensorUnitPrespectrumMap j)
      (boundedFlatPerfectSupportedTensorUnitPrespectrumMap j) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (boundedFlatPerfectSupportedTensorUnit_exact j)
    (boundedFlatPerfectSupportedTensorUnit_exact j)
    (boundedFlatPerfectSupportedTensorUnitAutomorphism j r)

/-- The full original supported scalar loop, before any stable-localization quotient. -/
def boundedFlatPerfectSupportedGlobalUnitHomotopy (r : (Γ(X, ⊤))ˣ) :
    Homotopy (boundedFlatPerfectSupportedIdentityPrespectrumMap j)
      (boundedFlatPerfectSupportedIdentityPrespectrumMap j) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (Waldhausen.IsExact.id _ _)
    (Waldhausen.IsExact.id _ _) (boundedFlatPerfectSupportedGlobalUnitIso j r)

/-- The genuine supported tensor unitor gives the original coherent spectrum comparison. -/
def boundedFlatPerfectSupportedTensorUnitUnitorHomotopy :
    Homotopy (boundedFlatPerfectSupportedTensorUnitPrespectrumMap j)
      (boundedFlatPerfectSupportedIdentityPrespectrumMap j) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (boundedFlatPerfectSupportedTensorUnit_exact j)
    (Waldhausen.IsExact.id _ _) (boundedFlatPerfectSupportedTensorUnitIso j)

/-- The unchanged supported tensor/scalar square supplies the whole relative iterated-S prism. -/
def boundedFlatPerfectSupportedTensorUnitUnitorPasting (r : (Γ(X, ⊤))ˣ) :
    ((boundedFlatPerfectSupportedTensorUnitHomotopy j r).trans
      (boundedFlatPerfectSupportedTensorUnitUnitorHomotopy j)).RelHomotopy
      ((boundedFlatPerfectSupportedTensorUnitUnitorHomotopy j).trans
        (boundedFlatPerfectSupportedGlobalUnitHomotopy j r)) :=
  exactOriginalPrespectrumPastingHomotopy _ _
    (boundedFlatPerfectSupportedTensorUnit_exact j) (boundedFlatPerfectSupportedTensorUnit_exact j)
    (Waldhausen.IsExact.id _ _) (Waldhausen.IsExact.id _ _)
    (boundedFlatPerfectSupportedTensorUnitAutomorphism j r).hom
    (boundedFlatPerfectSupportedTensorUnitIso j).hom
    (boundedFlatPerfectSupportedTensorUnitIso j).hom
    (boundedFlatPerfectSupportedGlobalUnitIso j r).hom
    (fun _ ↦ (boundedFlatPerfectSupportedWaldhausen j).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectSupportedWaldhausen j).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectSupportedWaldhausen j).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectSupportedWaldhausen j).weq_iso _ inferInstance)
    (boundedFlatPerfectSupportedTensorUnitAutomorphism_unitor j r)

end Quillen.PerfectComplexes
