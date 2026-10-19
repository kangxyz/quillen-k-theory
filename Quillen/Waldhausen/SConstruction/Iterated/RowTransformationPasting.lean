/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationSpectrum
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumPastingHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! # Endpoint-relative pasting of genuine first-row cells

The original Model transformation square is realized before postcomposition by the genuine
row map. The comparison, unit, row and degree-zero input-loop coordinates remain independent.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} {F G G' H : V ⟶ W}
  (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
  (η' : F.functor ⟶ G'.functor) (θ' : G'.functor ⟶ H.functor)
  (hη : ∀ A, W.waldhausen.weq (η.app A))
  (hθ : ∀ A, W.waldhausen.weq (θ.app A))
  (hη' : ∀ A, W.waldhausen.weq (η'.app A))
  (hθ' : ∀ A, W.waldhausen.weq (θ'.app A))
  (hcomp : η ≫ θ = η' ≫ θ')

/-- The actual first-row endpoint-relative prism of the supplied transformation square. -/
def rowTransformationPasting :=
  (prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' hcomp).postcomp
    (rowStabilizationMap W)

/-- Postcomposition preserves the original concatenation boundary without retiming either cell. -/
theorem rowTransformationPasting_boundary :
    ((prespectrumTransformationHomotopy η hη).trans
      (prespectrumTransformationHomotopy θ hθ)).postcomp (rowStabilizationMap W) =
    (rowTransformationSpectrumHomotopy η hη).trans
      (rowTransformationSpectrumHomotopy θ hθ) :=
  Homotopy.postcomp_trans _ _ _

/-- Positive levels keep the comparison, unit and first-row times separate. -/
theorem rowTransformationPasting_succ (k : ℕ) (r t s : unitInterval)
    (x : stageSpace k V) :
    Path.toContinuousMap
      ((rowTransformationPasting η θ η' θ' hη hθ hη' hθ' hcomp).level
        (k + 1) (r, (t, x))) s =
    (prespectrum W).structureMap (k + 1)
      ((prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' hcomp).level
        (k + 1) (r, (t, x))) s := rfl

/-- Degree zero preserves its original input loop and the independent first-row coordinate. -/
theorem rowTransformationPasting_zero (r t a s : unitInterval)
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    Path.toContinuousMap
      (Path.toContinuousMap
        ((rowTransformationPasting η θ η' θ' hη hθ hη' hθ' hcomp).level
          0 (r, (t, γ))) a) s =
    (prespectrum W).structureMap 1
      ((prespectrum W).structureMap 0
        ((prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' hcomp).level
          0 (r, (t, γ))) a) s := rfl

end Quillen.Waldhausen.IteratedS
