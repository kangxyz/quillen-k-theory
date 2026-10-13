/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveQLoopComponentProduct

/-!
# Independent actual Q-loop product consumer

The original compact-open Q loop space is genuinely homotopy equivalent to
its discrete original K₀ labels times its actual constant-loop component.
This consumes both inverse homotopies, exact neutral inclusion, the positive
stage label, and ordinary naturality under an arbitrary unital ring map.
No BGL-plus identification of the neutral factor is assumed.
-/

@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
open scoped Topology
universe u
namespace Consumer.QLoopComponentProduct

variable (R : Type u) [Ring R]

/-- An actual continuous inverse path after decomposing an original loop and reconstructing it. -/
def reconstructOriginalLoop
    (γ : Path (exactStructure.{u, u} R).kBasepoint (exactStructure R).kBasepoint) :
    Path ((originalQLoopProductEquiv R).invFun (originalQLoopProductEquiv R γ)) γ :=
  (originalQLoopProductEquiv R).left_inv.some.evalAt γ

/-- The other inverse path acts on the actual discrete-label times neutral-component product. -/
def decomposeOriginalProduct
    (z : (exactStructure.{u, u} R).DiscreteKZero × (exactStructure R).QLoopIdentityComponent) :
    Path (originalQLoopProductEquiv R ((originalQLoopProductEquiv R).invFun z)) z :=
  (originalQLoopProductEquiv R).right_inv.some.evalAt z

/-- The standard right-module stage coordinate is positive numerator-minus-denominator. -/
theorem stage_coordinate (n : ℕ) (P : IsoCategory Rᵐᵒᵖ) :
    ((originalQLoopProductEquiv Rᵐᵒᵖ
      (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0)
        (classifyingSpacePoint (completionPair Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) P)))).1).ofTopology =
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass P.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass (rankOnePower Rᵐᵒᵖ n).of :=
  originalQLoopProductEquiv_stage_label R n P

variable {R} {S : Type u} [Ring S]

/-- Unital right-module base change respects normalized products up to actual homotopy. -/
theorem baseChange_naturality (f : R →+* S) :
    ((basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
      (rightBaseChangeExact f).normalizedQ_map_point).comp
        (exactStructure.{u, u} Rᵐᵒᵖ).qLoopComponentProductEquiv.toFun).Homotopic
      ((exactStructure.{u, u} Sᵐᵒᵖ).qLoopComponentProductEquiv.toFun.comp
        (loopComponentProductChange (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
          (rightBaseChangeExact f).normalizedQ_map_point
          (rightBaseChangeExact f).discreteKZeroMap)) :=
  (rightBaseChangeExact f).qLoopComponentProductEquiv_naturality

end Consumer.QLoopComponentProduct
