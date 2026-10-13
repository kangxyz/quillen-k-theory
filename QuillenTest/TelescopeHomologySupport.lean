/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.Topology.LocalCoefficients.TelescopeHomologySupport
import Quillen.Topology.LocalCoefficients.TelescopeHomologyDiagram

/-! # Original-stage support and homology-colimit regression checks -/

open CategoryTheory CategoryTheory.Limits Quillen Quillen.LocalCoefficients
open Quillen.GrothendieckTelescope
universe u
noncomputable section

example (F : ℕ ⥤ Cat.{u, u})
    (A : System.{u, u} (ClassifyingSpace (Model F))) (d : ℕ) :
    IsColimit (stageHomologyCocone F A d) := stageHomologyIsColimit F A d

example (F : ℕ ⥤ Cat.{u, u})
    (A : System.{u, u} (ClassifyingSpace (Model F))) (d : ℕ)
    {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    stageHomologyTransition F (h.trans h') A d =
      stageHomologyTransition F h A d ≫ stageHomologyTransition F h' A d :=
  stageHomologyTransition_comp F A d h h'

example (F : ℕ ⥤ Cat.{u, u}) (n : ℕ)
    (A : System.{u, u} (ClassifyingSpace (Model F))) (d : ℕ)
    (x : homology (pullback (classifyingSpaceMap (Grothendieck.ι F n)).hom A) d) :
    ∃ (m : ℕ) (h : n ≤ m) (s : Finset (ClassifyingSpace (F.obj m))),
      (∀ a ∈ s, ∀ b ∈ s,
        Joined (classifyingSpaceMap (Grothendieck.ι F m) a)
          (classifyingSpaceMap (Grothendieck.ι F m) b) → Joined a b) ∧
      (∀ (B : System.{u, u} (ClassifyingSpace (F.obj m)))
        (η θ : pullback (classifyingSpaceMap (Grothendieck.ι F m)).hom A ⟶ B),
        (∀ p ∈ s, η.app (FundamentalGroupoid.mk p) = θ.app (FundamentalGroupoid.mk p)) →
        coefficientHomologyMap η d (stageHomologyTransition F h A d x) =
          coefficientHomologyMap θ d (stageHomologyTransition F h A d x)) :=
  localHomology_stage_finite_support_stabilizes F n A d x
