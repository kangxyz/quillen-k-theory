/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.Topology.LocalCoefficients.FilteredHomologyElements

/-! The representative and vanishing criteria retain original spatial maps. -/

open CategoryTheory Limits Quillen.LocalCoefficients
open scoped Simplicial
noncomputable section
universe u
variable {J : Type u} [SmallCategory J] [IsFiltered J]

example (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) (n : ℕ) (x : homology A n) :
    ∃ (j : J) (y : (filteredHomologyDiagram F c A n).obj j),
      pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom A n y = x :=
  filteredHomology_exists_stage F c hc A n x

example (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) (n : ℕ) (j : J)
    (x : (filteredHomologyDiagram F c A n).obj j)
    (h : pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom A n x = 0) :
    ∃ (k : J) (f : j ⟶ k), (filteredHomologyDiagram F c A n).map f x = 0 :=
  (filteredHomology_eq_zero_iff F c hc A n x).mp h
