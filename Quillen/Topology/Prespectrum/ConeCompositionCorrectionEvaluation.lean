/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.ConeCompositionPieces
public import Quillen.Topology.Prespectrum.RelativeHomotopyAssociatorEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyTerminalEvaluation

/-! Evaluation of the exact original correction, retaining its ofLevels endpoint witnesses. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.ConeCompositionPieces
variable {E F E' F' E'' F'' : LoopPrespectrum.{u}}
  {f : E ⟶ F} {g : E' ⟶ F'} (h : E'' ⟶ F'')
  (a : E ⟶ E') {b : F ⟶ F'} (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))

/-- The original R comparison is the same scalar associator at every native input and time. -/
theorem correction_apply (n : ℕ) (r s : I) (x : E.space n) :
    (coneSquareCompositionNullComparison f g h a b c d H K).level n (r, (s, x)) =
    Path.Homotopy.transAssoc ((first h a d H).path n x)
      ((second h a c d K).path n x) ((third h a c).path n x) (r, s) := by
  have hv : (coneSquareCompositionNullComparison f g h a b c d H K).level n
      (r, (s, x)) =
      (Homotopy.RelHomotopy.transAssoc
        (first h a d H) (second h a c d K) (third h a c)).level n (r, (s, x)) := rfl
  exact hv.trans (Homotopy.RelHomotopy.transAssoc_apply_path
    (first h a d H) (second h a c d K) (third h a c) n r s x)

end Quillen.LoopPrespectrum.ConeCompositionPieces
