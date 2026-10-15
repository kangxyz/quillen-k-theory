/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ReferenceWhiskeringFamily

/-! The original source and target projection binary rows, retaining their actual references. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH0Merge

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassH0Merge

theorem anchorNode_refl {V W : Model.{u}} {F : V ⟶ W}
    (N : Σ G : V ⟶ W, F.functor ≅ G.functor) : anchorNode (Iso.refl F.functor) N = N := by
  rcases N with ⟨G, ρ⟩
  exact congrArg (fun η : F.functor ≅ G.functor ↦
    (⟨G, η⟩ : Σ G : V ⟶ W, F.functor ≅ G.functor)) (Iso.refl_trans ρ)

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)

/-- The complete original source binary column, with its literal projection anchor. -/
theorem native_source_column (i : Fin 3) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr (rectangleLeftIndex i) =
      binaryColumnNode (ProjectionReference.reference c r) c q p
        (ProjectionReference.anchor p q c r hr) i := by
  have he : projectionLeftNode p q p' q' a b c hp hq r hr
      (ProjectionReference.reference c r) rfl i =
      ProjectionReference.nodes p q p' q' a b c hp hq r hr (rectangleLeftIndex i) :=
    anchorNode_refl _
  exact he.symm.trans (projection_left_column p q p' q' a b c hp hq r hr
    (ProjectionReference.reference c r) rfl i)

/--
The reference from the projection anchor to the last normalized triple, induced by the total
commuting-square equality.
-/
def nativeLastReference : (ProjectionReference.reference c r).functor ≅
    (NormalizedTripleSimplex.sourceMap q' p' a).functor :=
  eqToIso (ProjectionReference.anchor p q c r hr) ≪≫
    DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq

/-- Every actual last-triple node keeps the unchanged total-square equality transport. -/
theorem native_last_nodes (i : Fin 8) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr
      (DoubleSquareMergedSimplex.lastFace.toOrderHom i) =
    (⟨SplitTripleSimplex.vertices q' p' a i,
      nativeLastReference p q p' q' a b c hp hq r hr ≪≫
        SplitTripleSimplex.references q' p' a i⟩ : ProjectionReference.Node c r) := by
  have hn := anchorNode_congr
    (F₀ := ProjectionReference.reference c r) (F₁ := NormalizedTripleSimplex.sourceMap c q p)
    (eqToIso (ProjectionReference.anchor p q c r hr))
    ((DoubleSquareMergedSimplex.last_nodes p q p' q' a b c hp hq i).trans
      (DoubleSquareCommonSimplex.last_nodes p q p' q' a b c hp hq i))
  exact hn.trans (anchorNode_assoc
    (F₀ := ProjectionReference.reference c r) (F₁ := NormalizedTripleSimplex.sourceMap c q p)
    (F₂ := NormalizedTripleSimplex.sourceMap q' p' a)
    (eqToIso (ProjectionReference.anchor p q c r hr))
    (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq)
    ⟨SplitTripleSimplex.vertices q' p' a i, SplitTripleSimplex.references q' p' a i⟩)

/-- The entire target projection row retains both original binary normalization pieces. -/
theorem native_target_row (i : Fin 3) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
      preBinaryNodes (ProjectionReference.reference c r) (normalizedMap a) q' p'
        (rightRowReference (ProjectionReference.reference c r) q' p' a
          (nativeLastReference p q p' q' a b c hp hq r hr)) i :=
  (native_last_nodes p q p' q' a b c hp hq r hr (rightIndex i)).trans
    (triple_right_row (ProjectionReference.reference c r) q' p' a
      (nativeLastReference p q p' q' a b c hp hq r hr) i)

end Quillen.PerfectComplexes.BassH1Join
