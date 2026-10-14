/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MPrimitiveSupport

/-! Native family preservation through actual full nodes and their ordered support faces. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes.BassMFamilyTransfer
open BassH1Merged
variable {V W : Model.{u}} {p q k : ℕ}
  (F : V ⟶ W)
  (N : Fin (p + 1) → Σ G : V ⟶ W, F.functor ≅ G.functor)
  (M : Fin (q + 1) → Σ G : V ⟶ W, F.functor ≅ G.functor)
  (f : Fin (p + 1) → Fin (q + 1)) (hn : ∀ i, M (f i) = N i)

include hn in
/-- Every point on an actual ordered support retains its full original native family value. -/
theorem supported_value (α : ⦋k⦌ ⟶ ⦋p⦌) (h : Monotone (f ∘ α.toOrderHom))
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (ModelSimplex.ofIsos F (fun i ↦ (M i).1) (fun i ↦ (M i).2)) n
      (StdSimplex.map f (StdSimplex.map α.toOrderHom z), x) =
    prespectrumSimplexFamily (ModelSimplex.ofIsos F (fun i ↦ (N i).1) (fun i ↦ (N i).2)) n
      (StdSimplex.map α.toOrderHom z, x) := by
  rw [← StdSimplex.map_comp]
  change prespectrumSimplexFamily
    (ModelSimplex.ofIsos F (fun i ↦ (M i).1) (fun i ↦ (M i).2)) n
    (StdSimplex.map (supportedFace f α h).toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, supported_reference_face F N M f hn α h]
  exact (prespectrumSimplexFamily_face
    (ModelSimplex.ofIsos F (fun i ↦ (N i).1) (fun i ↦ (N i).2)) α n z x).symm

include hn in
/-- An old supported face and its new ordered image preserve every native parameter and input. -/
theorem composed_supported_value {r : ℕ} (g : Fin (r + 1) → Fin (p + 1))
    (α : ⦋k⦌ ⟶ ⦋r⦌) (hg : Monotone (g ∘ α.toOrderHom))
    (hfg : Monotone (f ∘ g ∘ α.toOrderHom))
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (ModelSimplex.ofIsos F (fun i ↦ (M i).1) (fun i ↦ (M i).2)) n
      (StdSimplex.map f (StdSimplex.map g (StdSimplex.map α.toOrderHom z)), x) =
    prespectrumSimplexFamily (ModelSimplex.ofIsos F (fun i ↦ (N i).1) (fun i ↦ (N i).2)) n
      (StdSimplex.map g (StdSimplex.map α.toOrderHom z), x) := by
  have he : StdSimplex.map g (StdSimplex.map α.toOrderHom z) =
      StdSimplex.map (supportedFace g α hg).toOrderHom z :=
    (StdSimplex.map_comp z α.toOrderHom g).symm
  rw [he]
  exact supported_value F N M f hn (supportedFace g α hg) hfg n z x

end Quillen.PerfectComplexes.BassMFamilyTransfer
