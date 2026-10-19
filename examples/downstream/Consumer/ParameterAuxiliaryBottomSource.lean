/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryBottomSource

/-! # Incoming actual Model maps retain the explicit bottom-source equality cast -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open ParameterAuxiliarySupport
universe u
namespace Consumer.ParameterAuxiliaryBottomSource

/-- The original source map equals the prescribed cast after any incoming exact Model map. -/
theorem toBasic_precompose (Q : Scheme.{u}) (U : Q.Opens) (X : Scheme.{u}ᵒᵖ)
    (h : unionOpen U.ι ⊥ = U) {A : Model.{u + 1}} (g : A ⟶ (fiber U.ι ⊥).obj X) :
    g ≫ (toBasic U.ι ⊥).app X =
      g ≫ (eqToHom
        (congrArg (fun V : Q.Opens => ParameterModels.supported V.ι) h)).app X :=
  congrArg (fun η => g ≫ η.app X) (toBasic_ι_bot_eqToHom U h)

end Consumer.ParameterAuxiliaryBottomSource
