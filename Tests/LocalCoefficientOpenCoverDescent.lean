/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.TwoOpenDescent

/-! Regression tests for genuine spatial local-to-global twisted homology. -/

@[expose] public section

noncomputable section

open CategoryTheory Quillen.LocalCoefficients

universe u v w

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

example (f : C(X, Y)) (U : Set X) (V : Set Y) (h : Set.MapsTo f U V)
    (A : System.{u, u} Y) :
    subspacePushforwardChainMap f U V h A ≫ (subspaceSmallChainIso V A).hom =
      (subspaceSmallChainIso U (pullback f A)).hom ≫
        smallPushforwardChainMap f (singletonCover U) (singletonCover V) A
          (fun hσ ↦ hσ.map id (fun _ ↦ h)) :=
  subspacePushforwardChainMap_smallChainIso f U V h A

example (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (A : System.{u, u} Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (openU : IsOpen U) (openV : IsOpen V) (coverX : U ∪ V = Set.univ)
    (openU' : IsOpen U') (openV' : IsOpen V') (coverY : U' ∪ V' = Set.univ)
    (h₁ : QuasiIso (subspacePushforwardChainMap f U U' hU A))
    (h₂ : QuasiIso (subspacePushforwardChainMap f V V' hV A))
    (h₁₂ : QuasiIso (subspacePushforwardChainMap f (U ∩ V) (U' ∩ V')
      (mapsTo_intersection f U V U' V' hU hV) A)) :
    QuasiIso (pushforwardChainMap f A) :=
  pushforwardChainMap_quasiIso_of_two_open_subspaces f U V U' V' A hU hV
    openU openV coverX openU' openV' coverY h₁ h₂ h₁₂

example (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (A : System.{u, u} Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (openU : IsOpen U) (openV : IsOpen V) (coverX : U ∪ V = Set.univ)
    (openU' : IsOpen U') (openV' : IsOpen V') (coverY : U' ∪ V' = Set.univ)
    (h₁ : QuasiIso (subspacePushforwardChainMap f U U' hU A))
    (h₂ : QuasiIso (subspacePushforwardChainMap f V V' hV A))
    (h₁₂ : QuasiIso (subspacePushforwardChainMap f (U ∩ V) (U' ∩ V')
      (mapsTo_intersection f U V U' V' hU hV) A)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (pushforwardChainMap f A) n) :=
  pushforwardHomologyMap_isIso_of_two_open_subspaces f U V U' V' A hU hV
    openU openV coverX openU' openV' coverY h₁ h₂ h₁₂ n

example {ι : Type v} {κ : Type w} (f : C(X, Y)) (U : ι → Set X) (V : κ → Set Y)
    (A : System.{u, u} Y)
    (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall V (f.comp σ)) :
    smallPushforwardChainMap f U V A h ≫ smallChainComplexInclusion V A =
      smallChainComplexInclusion U (pullback f A) ≫ pushforwardChainMap f A :=
  smallPushforwardChainMap_inclusion f U V A h
