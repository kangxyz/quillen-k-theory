/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.Topology.LocalCoefficients.TelescopeHomologyDetection
import Quillen.Topology.ClassifyingSpace.TelescopeComponents

/-! # Original stage maps detect local homology and finite component relations -/

open CategoryTheory Quillen Quillen.LocalCoefficients
open Quillen.GrothendieckTelescope
universe u

example (F : ℕ ⥤ Cat.{u, u}) (n : ℕ)
    (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ)
    (x : homology (pullback (classifyingSpaceMap (Grothendieck.ι F n)).hom A) k) :
    pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι F n)).hom A k x = 0 ↔
      ∃ (m : ℕ) (h : n ≤ m), stageHomologyTransition F h A k x = 0 :=
  localHomology_stage_eq_zero_iff F n A k x

example (F : ℕ ⥤ Cat.{u, u}) (n : ℕ) (s : Finset (ClassifyingSpace (F.obj n))) :
    ∃ (m : ℕ) (hnm : n ≤ m), ∀ x ∈ s, ∀ y ∈ s,
      Joined (classifyingSpaceMap (F.map (homOfLE hnm)).toFunctor x)
        (classifyingSpaceMap (F.map (homOfLE hnm)).toFunctor y) ↔
      Joined (classifyingSpaceMap (Grothendieck.ι F n) x)
        (classifyingSpaceMap (Grothendieck.ι F n) y) :=
  stage_finite_component_relations_stabilize F n s
