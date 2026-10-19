/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexWeakPrepend
public import Quillen.Waldhausen.SConstruction.Iterated.ScalarRouteExtraction

/-!
# Exact native recovery of the directed weak edge

The prepended edge has the original natural-transformation homotopy at every level and time.
The proof uses the already selected composition triangle and extracts its original first half;
it does not choose a new path between the same endpoints.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.ModelSimplex
variable {V W : Model.{u}} {k : ℕ} (S : ModelSimplex V W k) {F : V ⟶ W}
  (η : F.functor ⟶ (S.vertex 0).functor)
  (hη : ∀ X, W.waldhausen.weq (η.app X))

/-- All old parameters survive unchanged in the opposite face, including the old loop level. -/
theorem prependWeak_tail_native (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (prependWeak S η hη) n
      (StdSimplex.map Fin.succ z, x) = prespectrumSimplexFamily S n (z, x) := by
  change prespectrumSimplexFamily (prependWeak S η hη) n
    (StdSimplex.map tailFace.toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, prependWeak_tail]

/-- The original selected composition comparison is a complete directed triangle face. -/
theorem prependWeak_firstTriangle_native :
    HomotopyLift (prependWeak S η hη)
      (Quillen.SimplexParameters.triangle (firstEdgeTriangle (k := k)))
      (prespectrumTransformationCompositionHomotopy η (𝟙 _) hη
        (fun _ ↦ W.waldhausen.weq.id_mem _)) :=
  triangle_lift _ _ _ _ _ _ (prependWeak_firstTriangle S η hη)

/-- Every original weak-edge time is recovered, with no invertibility assumption. -/
theorem prependWeak_edge_native :
    PathLift (prependWeak S η hη) (edge 0 1)
      (prespectrumTransformationHomotopy η hη) :=
  PathLift.trans_left _
    (HomotopyLift.target _ (prependWeak_firstTriangle_native S η hη))

/-- Reversing the scalar edge reverses exactly the original weak-transformation time. -/
theorem prependWeak_reverse_native (n : ℕ) (r : unitInterval)
    (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (prependWeak S η hη) n
      ((edge (k := k + 1) 0 1).symm r, x) =
        (prespectrumTransformationHomotopy η hη).level n (unitInterval.symm r, x) :=
  prependWeak_edge_native S η hη n (unitInterval.symm r) x

end Quillen.Waldhausen.IteratedS.ModelSimplex
