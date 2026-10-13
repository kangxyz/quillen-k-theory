/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.TelescopeTransitions
public import QuillenTest.LocalCoefficientChains

/-!
# Consumers of the infinite categorical telescope

These checks retain the original unit, stabilization natural transformation,
and local-homology cocone arrows for a genuinely path-dependent system.
-/

@[expose] public section

open CategoryTheory Limits
noncomputable section
universe u

namespace QuillenTest.InfiniteCategoricalTelescope

open Quillen

open GrothendieckTelescope LocalCoefficients

variable (F : ℕ ⥤ Cat.{u, u})

/-- Every finite-prefix stage-zero unit is the same original infinite unit. -/
theorem original_unit (n : ℕ) :
    FiniteGrothendieckTelescope.inclusion F n 0 ⋙ prefixInclusion F n =
      Grothendieck.ι F 0 :=
  fiber_prefix_inclusion F n 0

/-- The stabilization transformation is already present in the finite prefix. -/
theorem original_transition {n m : ℕ} (h : n ≤ m) :
    Functor.whiskerRight (finiteStageTransitionNatTrans F h) (prefixInclusion F m) =
      stageTransitionNatTrans F h :=
  finiteStageTransitionNatTrans_infinite F h

/-- The actual regular-system homology comparison preserves each original prefix map. -/
theorem regular_original_arrow (b : ClassifyingSpace (Model F))
    (V : ModuleCat.{u} ℤ) (k n : ℕ) :
    colimit.ι (localHomologyDiagram F (LocalCoefficientChains.regularSystem b V) k)
        (AsSmall.up.obj n) ≫
        (localHomologyColimitIso F (LocalCoefficientChains.regularSystem b V) k).hom =
      pushforwardHomologyMap (classifyingSpaceMap (prefixInclusion F n)).hom
        (LocalCoefficientChains.regularSystem b V) k :=
  localHomologyColimitIso_ι_hom F _ k n

/-- Original stabilization maps commute after genuine, potentially nonconstant transport. -/
theorem regular_stage_transition {n m : ℕ} (h : n ≤ m)
    (b : ClassifyingSpace (Model F)) (V : ModuleCat.{u} ℤ) (k : ℕ) :
    stageHomologyTransition F h (LocalCoefficientChains.regularSystem b V) k ≫
        pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι F m)).hom
          (LocalCoefficientChains.regularSystem b V) k =
      pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι F n)).hom
        (LocalCoefficientChains.regularSystem b V) k :=
  stageHomologyTransition_to_infinite F h _ k

end QuillenTest.InfiniteCategoricalTelescope
