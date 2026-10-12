/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.Topology.LocalCoefficients.Homology

/-! Independent consumers of actual twisted homology and coefficient conversion. -/

open CategoryTheory Quillen.LocalCoefficients

universe u

noncomputable section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

example (A : System.{u, u} X) (n : ℕ) :
    coefficientHomologyMap (𝟙 A) n = 𝟙 (homology A n) := by simp

example (f : C(X, Y)) {A B : System.{u, u} Y} (e : A ≅ B) (n : ℕ) :
    pushforwardHomologyMap f B n =
      coefficientHomologyMap (pullbackMap f e.inv) n ≫
        pushforwardHomologyMap f A n ≫ coefficientHomologyMap e.hom n :=
  pushforwardHomologyMap_coefficient_iso f e n

example {f g : C(X, Y)} (H : f.Homotopy g) (A : System.{u, u} Y) (n : ℕ) :
    homology (pullback f A) n ≅ homology (pullback g A) n :=
  homotopyPullbackHomologyIso H A n

example (V : ModuleCat.{u} ℤ) (n : ℕ) :
    homology (constant X V) n ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj V).obj
        (TopCat.of X) :=
  constantHomologyIso V n

example (V : ModuleCat.{0} ℤ) :
    homology (constant PUnit V) 0 ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj V).obj
        (TopCat.of PUnit) :=
  constantHomologyIso V 0
