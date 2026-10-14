/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexIsomorphism
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexPrespectrum

/-! Exact parameter lifts of the old whole composition triangles, at every original level. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} {k l : ℕ}

/-- Barycentric face transport retains the complete original family. -/
theorem prespectrumSimplexFamily_face (S : ModelSimplex V W k)
    (α : ⦋l⦌ ⟶ ⦋k⦌) (n : ℕ) (z : StdSimplex ℝ (Fin (l + 1)))
    (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (StdSimplex.map α.toOrderHom z, x) =
      prespectrumSimplexFamily (S.face α) n (z, x) := by
  have hs (r : ℕ) (y : stageSpace r V) :
      stageSimplexBarycentric S r (StdSimplex.map α.toOrderHom z, y) =
        stageSimplexBarycentric (S.face α) r (z, y) := by
    unfold stageSimplexBarycentric
    dsimp only [ContinuousMap.coe_mk]
    have hz : (SimplexCategory.toTopHomeo ⦋k⦌).symm
        (StdSimplex.map α.toOrderHom z) =
        SSet.toTop.map (SSet.stdSimplex.map α)
          ((SimplexCategory.toTopHomeo ⦋l⦌).symm z) := by
      apply (SimplexCategory.toTopHomeo ⦋k⦌).injective
      rw [Homeomorph.apply_symm_apply, SimplexCategory.toTopHomeo_naturality_apply,
        Homeomorph.apply_symm_apply]
      rfl
    rw [hz]
    exact stageSimplexRealization_face r S α y _
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext t
    exact hs 0 (x t)
  | succ n => exact hs n x

/-- The old full composition triangle is the common simplex evaluated at its actual parameters.
This includes its degree-zero loop family; no time coordinate is collapsed. -/
theorem prespectrumSimplexFamily_triangle {F G H : V ⟶ W}
    (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (ModelSimplex.triangle η θ hη hθ) n
      (Quillen.TheoremB.compositionTriangleHomotopy (r, s), x) =
        (prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (s, x)) := by
  have hs (j : ℕ) (y : stageSpace j V) :
      stageSimplexBarycentric (ModelSimplex.triangle η θ hη hθ) j
        (Quillen.TheoremB.compositionTriangleHomotopy (r, s), y) =
        stageTransformationCompositionHomotopy η θ hη hθ j (r, (s, y)) := by
    exact DFunLike.congr_fun (stageSimplexRealization_triangle j η θ hη hθ) _
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext t
    exact hs 0 (x t)
  | succ n => exact hs n x

/-- Two actual component equations place an old whole relative composition in one common family. -/
theorem prespectrumSimplexFamily_ofIsos_triangle
    (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (F i).functor) (α : ⦋2⦌ ⟶ ⦋k⦌)
    (η : (F (α.toOrderHom 0)).functor ⟶ (F (α.toOrderHom 1)).functor)
    (θ : (F (α.toOrderHom 1)).functor ⟶ (F (α.toOrderHom 2)).functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))
    (eη : (ρ (α.toOrderHom 0)).hom ≫ η = (ρ (α.toOrderHom 1)).hom)
    (eθ : (ρ (α.toOrderHom 1)).hom ≫ θ = (ρ (α.toOrderHom 2)).hom)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (ModelSimplex.ofIsos F₀ F ρ) n
      (StdSimplex.map α.toOrderHom (Quillen.TheoremB.compositionTriangleHomotopy (r, s)), x) =
        (prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (s, x)) := by
  rw [prespectrumSimplexFamily_face,
    ModelSimplex.ofIsos_face_triangle F₀ F ρ α η θ hη hθ eη eθ]
  exact prespectrumSimplexFamily_triangle η θ hη hθ n r s x

end Quillen.Waldhausen.IteratedS
