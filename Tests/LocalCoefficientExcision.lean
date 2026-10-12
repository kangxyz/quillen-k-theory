/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.MayerVietoris

/-! Regression tests for actual all-local-system gluing and excision. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits Quillen.LocalCoefficients

universe u v w

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {κ : Type w}

example (U : ι → Set X) (V : κ → Set X) (A : System.{u, u} X) :
    (smallChainGluingSequence U V A).ShortExact :=
  smallChainGluingSequence_shortExact U V A

example (U : ι → Set X) (V : κ → Set X) (A : System.{u, u} X) :
    IsPushout (intersectionChainLeft U V A) (intersectionChainRight U V A)
      (unionChainLeft U V A) (unionChainRight U V A) :=
  smallChainGluing_isPushout U V A

example (U : ι → Set X) (V : κ → Set X) (A : System.{u, u} X) :
    IsIso (smallChainQuotientMap U V A) := inferInstance

example (U : ι → Set X) (V : κ → Set X) (A : System.{u, u} X)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j))
    (hcover : ∀ x, (∃ i, x ∈ U i) ∨ (∃ j, x ∈ V j)) :
    QuasiIso (smallChainExcisionMap U V A) :=
  smallChainExcisionMap_quasiIso U V A hU hV hcover

example (U : Set X) (A : System.{u, u} X) :
    (subspaceSmallChainIso U A).hom ≫ smallChainComplexInclusion (singletonCover U) A =
      pushforwardChainMap (subspaceInclusion U) A :=
  subspaceSmallChainIso_hom_inclusion U A

example (U : Set X) (A : System.{u, u} X) :
    Mono (pushforwardChainMap (subspaceInclusion U) A) := inferInstance

example (U V : Set X) (A : System.{u, u} X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (openExcisionChainMap U V A) :=
  openExcisionChainMap_quasiIso U V A hU hV hcover

example (U V : Set X) (A : System.{u, u} X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (openExcisionChainMap U V A) n) :=
  openExcisionChainMap_homology_isIso U V A hU hV hcover n

example (U : ι → Set X) (V : κ → Set X) (A : System.{u, u} X)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j))
    (hcover : ∀ x, (∃ i, x ∈ U i) ∨ (∃ j, x ∈ V j)) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (mayerVietorisAssembly U V A) (n + 1))
      (mayerVietorisBoundary U V A hU hV hcover n)
      (mayerVietorisAssembly_boundary U V A hU hV hcover n)).Exact :=
  mayerVietoris_exact_ambient U V A hU hV hcover n

example (U : ι → Set X) (V : κ → Set X) (A : System.{u, u} X)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j))
    (hcover : ∀ x, (∃ i, x ∈ U i) ∨ (∃ j, x ∈ V j)) (n : ℕ) :
    (ShortComplex.mk (mayerVietorisBoundary U V A hU hV hcover n)
      (HomologicalComplex.homologyMap (smallChainGluingDifference U V A) n)
      (mayerVietorisBoundary_difference U V A hU hV hcover n)).Exact :=
  mayerVietoris_exact_intersection U V A hU hV hcover n
