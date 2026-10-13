/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.PosetLoop
public import Quillen.Topology.ClassifyingSpace.ProjectiveCompletionLoops

/-!
# The original Q loop target has an actual poset-loop model

For every ring, including the zero ring and noncommutative rings, the literal
loop target used by the original completion comparison is homotopy equivalent
to loops of the proved poset resolution. This client retains the exact
constant loop and explicitly witnesses both inverse homotopies.
-/

@[expose] public section
noncomputable section

open CategoryTheory Quillen Quillen.FiniteProjectiveModule Quillen.RankedChainOrder
open scoped Topology unitInterval ZeroObject

universe u
namespace Consumer.PosetLoop

variable (R : Type u) [Ring R]

/-- The actual canonical point of the poset resolution of the original Q category. -/
def originalQPosetPoint :=
  classifyingSpacePoint
    (universalResolutionVertex (exactStructure R).QCategory (exactStructure R).qZero)

/-- A genuine equivalence to the unchanged target of the original comparison. -/
def originalQLoopEquiv :
    ContinuousMap.HomotopyEquiv
      (Path (originalQPosetPoint R) (originalQPosetPoint R))
      (Path (classifyingSpacePoint (exactStructure R).qZero)
        (classifyingSpacePoint (exactStructure R).qZero)) :=
  universalResolutionLoopHomotopyEquiv (exactStructure R).QCategory (exactStructure R).qZero

/-- No basepoint path correction is hidden in this poset-loop reduction. -/
theorem originalQLoopEquiv_refl :
    originalQLoopEquiv R (Path.refl (originalQPosetPoint R)) =
      Path.refl (classifyingSpacePoint (exactStructure R).qZero) :=
  universalResolutionLoopHomotopyEquiv_refl (exactStructure R).QCategory (exactStructure R).qZero

/-- Every original Q loop has its actual inverse-composite path. -/
def originalQLoopInversePath
    (γ : Path (classifyingSpacePoint (exactStructure R).qZero)
      (classifyingSpacePoint (exactStructure R).qZero)) :
    Path (originalQLoopEquiv R ((originalQLoopEquiv R).invFun γ)) γ :=
  (originalQLoopEquiv R).right_inv.some.evalAt γ

/-- Every loop in the actual poset model has the other inverse-composite path. -/
def posetLoopInversePath (γ : Path (originalQPosetPoint R) (originalQPosetPoint R)) :
    Path ((originalQLoopEquiv R).invFun (originalQLoopEquiv R γ)) γ :=
  (originalQLoopEquiv R).left_inv.some.evalAt γ

end Consumer.PosetLoop
