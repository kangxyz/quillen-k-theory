/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.DoubleCylinderTwistedHomology

/-! # Fresh arbitrary-system and unreduced-degree regressions -/
@[expose] public section

open Quillen.DoubleCylinder
open Quillen.LocalCoefficients

noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval
universe u
namespace QuillenTest.N4TwistedCylinder

open Quillen
open LocalCoefficients DoubleCylinder

/-- This exact comparison changes no space or coefficient universe. -/
theorem sameUniverseChainBridge {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (V : System.{u, u} Y) :
    QuasiIso (UniverseLift.chainMap.{u, u, u} f V) ↔ QuasiIso (pushforwardChainMap f V) :=
  UniverseLift.quasiIso_chainMap_iff f V

/-- Relative acyclicity also controls the original unreduced degree zero. -/
theorem relativeDegreeZero {X : Type u} [TopologicalSpace X]
    (U : Set X) (V : System.{u, u} X) (h : (relativeSingularChainComplex U V).Acyclic) :
    IsIso (HomologicalComplex.homologyMap (pushforwardChainMap (subspaceInclusion U) V) 0) := by
  let := pushforwardChainMap_quasiIso_of_relative_acyclic U V h
  infer_instance

/-- The same theorem controls an actual positive degree without a new condition. -/
theorem relativeDegreeOne {X : Type u} [TopologicalSpace X]
    (U : Set X) (V : System.{u, u} X) (h : (relativeSingularChainComplex U V).Acyclic) :
    IsIso (HomologicalComplex.homologyMap (pushforwardChainMap (subspaceInclusion U) V) 1) := by
  let := pushforwardChainMap_quasiIso_of_relative_acyclic U V h
  infer_instance

/-- The opposite square uses arbitrary systems and genuine vertical equivalences. -/
theorem arbitraryOppositeSquare {X Y X' Y' : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (s : ContinuousMap.HomotopyEquiv X' X) (p : ContinuousMap.HomotopyEquiv Y' Y)
    (f : C(X, Y)) (g : C(X', Y')) (w : p.toFun.comp g = f.comp s.toFun)
    (hf : ∀ V : System.{u, u} Y, QuasiIso (pushforwardChainMap f V))
    (V : System.{u, u} Y') : QuasiIso (pushforwardChainMap g V) :=
  pushforwardChainMap_quasiIso_of_equivalence_square s p f g w hf V

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (intervalEndpoints A) (endMap f g) l e)
variable (lo hi : unitInterval) (b : Band lo hi)

include sq b in
/-- Every actual pushout system is preserved by the left leg using g's hypothesis. -/
theorem arbitraryOriginalLeftLeg
    (hg : ∀ V : System.{u, u} C, QuasiIso (UniverseLift.chainMap g.hom V))
    (V : System.{u, u} D) : QuasiIso (UniverseLift.chainMap (gapLeftEndpoint e) V) :=
  doubleCylinder_leftEnd_universeLift_quasiIso f g sq lo hi b hg V

include sq b in
/-- Every actual pushout system is preserved by the right leg using f's hypothesis. -/
theorem arbitraryOriginalRightLeg
    (hf : ∀ V : System.{u, u} B, QuasiIso (UniverseLift.chainMap f.hom V))
    (V : System.{u, u} D) : QuasiIso (UniverseLift.chainMap (gapRightEndpoint e) V) :=
  doubleCylinder_rightEnd_universeLift_quasiIso f g sq lo hi b hf V

end QuillenTest.N4TwistedCylinder
