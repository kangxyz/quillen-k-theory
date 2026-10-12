/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.Topology.LocalCoefficients.UniverseLift
import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCompletion

/-! Independent consumers in unrelated universes, including the original stable matrix map. -/

open CategoryTheory Quillen.LocalCoefficients
open scoped Simplicial

universe u v w

noncomputable section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

example (f : C(X, Y)) (A : System.{v, w} Y) :
    UniverseLift.chainComplex.{u, w, v} (pullback f A) ⟶
      UniverseLift.chainComplex.{v, w, u} A :=
  UniverseLift.chainMap f A

example (f : C(X, Y)) (A : System.{v, w} Y) (n : ℕ) :
    UniverseLift.homology.{u, w, v} (pullback f A) n ⟶
      UniverseLift.homology.{v, w, u} A n :=
  UniverseLift.homologyMap f A n

example (f : C(X, Y)) (A : System.{v, w} Y) (n : ℕ)
    (σ : SingularSimplex (ULift.{max v w} X) ⦋n⦌) :
    chainInclusion (UniverseLift.system.{u, w, v} (pullback f A)) σ ≫
        (UniverseLift.chainMap f A).f n =
      chainInclusion (UniverseLift.system.{v, w, u} A)
        ((UniverseLift.map.{u, v, w} f).comp σ) :=
  UniverseLift.chainInclusion_chainMap f A σ

example (A : System.{u, w} X) (n : ℕ) :
    (UniverseLift.chainComplex.{u, w, v} A).d (n + 2) (n + 1) ≫
      (UniverseLift.chainComplex.{u, w, v} A).d (n + 1) n = 0 :=
  (UniverseLift.chainComplex.{u, w, v} A).d_comp_d _ _ _

example {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]
    (f : C(S, T)) (A : System.{u, u} T) :
    UniverseLift.chainMap f A ≫ (UniverseLift.chainComparisonIso A).hom =
      (UniverseLift.chainComparisonIso (pullback f A)).hom ≫ pushforwardChainMap f A :=
  UniverseLift.chainComparisonIso_naturality f A

example {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]
    (f : C(S, T)) (A : System.{u, u} T) (n : ℕ) :
    IsIso (UniverseLift.homologyMap f A n) ↔ IsIso (pushforwardHomologyMap f A n) :=
  UniverseLift.isIso_homologyMap_iff f A n

open Quillen.FiniteProjectiveModule.StableCompletion

example (R : Type u) [Ring R] (A : System.{u + 1, w} (ZeroComponent R)) (n : ℕ) :
    UniverseLift.homology.{u, w, u + 1} (pullback (stableZeroMap R) A) n ⟶
      UniverseLift.homology.{u + 1, w, u} A n :=
  UniverseLift.homologyMap (stableZeroMap R) A n

example (R : Type u) [Ring R] (A : System.{u + 1, w} (ZeroComponent R)) (n : ℕ) :
    IsIso (UniverseLift.homologyMap (stableZeroMap R) A n) ↔
      IsIso (pushforwardHomologyMap (UniverseLift.map.{u, u + 1, w} (stableZeroMap R))
        (UniverseLift.system.{u + 1, w, u} A) n) :=
  UniverseLift.isIso_homologyMap_iff_lifted (stableZeroMap R) A n
