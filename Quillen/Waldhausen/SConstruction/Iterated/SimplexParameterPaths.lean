/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleLift

/-! Exact scalar paths and old triangle parameter surfaces inside one finite simplex. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.SimplexParameters
variable {k : ℕ}

/-- The affine path along an arbitrary edge of the common simplex. -/
def edge (i j : Fin (k + 1)) :
    Path (StdSimplex.single i : StdSimplex ℝ (Fin (k + 1))) (StdSimplex.single j) where
  toFun t := StdSimplex.duple i j (unitInterval.nonneg (unitInterval.symm t))
    (unitInterval.nonneg t) (by simp)
  continuous_toFun := StdSimplex.continuous_duple i j
  source' := by
    apply StdSimplex.ext
    simp [StdSimplex.duple]
  target' := by
    apply StdSimplex.ext
    simp [StdSimplex.duple]

theorem map_triangle_edge (α : ⦋2⦌ ⟶ ⦋k⦌) (i j : Fin 3) (t : unitInterval) :
    StdSimplex.map α.toOrderHom (TheoremB.triangleEdge i j t) =
      edge (α.toOrderHom i) (α.toOrderHom j) t := by
  exact StdSimplex.map_duple _ _ _ _ _ _

/-- The original triangle homotopy with exactly the old dyadic composition parameter. -/
def triangle (α : ⦋2⦌ ⟶ ⦋k⦌) :
    (edge (α.toOrderHom 0) (α.toOrderHom 2)).Homotopy
      ((edge (α.toOrderHom 0) (α.toOrderHom 1)).trans
        (edge (α.toOrderHom 1) (α.toOrderHom 2))) where
  toFun z := StdSimplex.map α.toOrderHom (TheoremB.compositionTriangleHomotopy z)
  continuous_toFun := by fun_prop
  map_zero_left t := by
    rw [TheoremB.compositionTriangleHomotopy.apply_zero]
    exact map_triangle_edge α 0 2 t
  map_one_left t := by
    rw [TheoremB.compositionTriangleHomotopy.apply_one]
    change StdSimplex.map α.toOrderHom
      (((TheoremB.triangleEdgePath 0 1).trans (TheoremB.triangleEdgePath 1 2)) t) =
        ((edge (α.toOrderHom 0) (α.toOrderHom 1)).trans
          (edge (α.toOrderHom 1) (α.toOrderHom 2))) t
    rw [Path.trans_apply, Path.trans_apply]
    split <;> exact map_triangle_edge α _ _ _
  prop' r t ht := by
    change StdSimplex.map α.toOrderHom (TheoremB.compositionTriangleHomotopy (r, t)) = _
    rw [TheoremB.compositionTriangleHomotopy.eq_fst r ht]
    exact map_triangle_edge α 0 2 t

/-- Evaluation retains the entire old composition comparison, including its loop-space level. -/
theorem triangle_lift {V W : Waldhausen.IteratedS.Model.{u}}
    (S : Waldhausen.IteratedS.ModelSimplex V W k) (α : ⦋2⦌ ⟶ ⦋k⦌)
    {F G H : V ⟶ W} (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))
    (he : S.face α = Waldhausen.IteratedS.ModelSimplex.triangle η θ hη hθ)
    (n : ℕ) (r s : unitInterval) (x : (Waldhausen.IteratedS.prespectrum V).space n) :
    Waldhausen.IteratedS.prespectrumSimplexFamily S n (triangle α (r, s), x) =
      (Waldhausen.IteratedS.prespectrumTransformationCompositionHomotopy η θ hη hθ).level n
        (r, (s, x)) := by
  change Waldhausen.IteratedS.prespectrumSimplexFamily S n
    (StdSimplex.map α.toOrderHom (TheoremB.compositionTriangleHomotopy (r, s)), x) = _
  rw [Waldhausen.IteratedS.prespectrumSimplexFamily_face, he]
  exact Waldhausen.IteratedS.prespectrumSimplexFamily_triangle η θ hη hθ n r s x

end Quillen.SimplexParameters
