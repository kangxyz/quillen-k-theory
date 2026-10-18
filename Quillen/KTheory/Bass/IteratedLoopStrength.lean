/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.FiniteConeStrength
public import Quillen.Topology.Prespectrum.LoopTranspose

/-!
# The fixed-order finite iteration of the original loop strength

The original strength components give an actual natural transformation. Its iteration uses
`kappa_(Omega^j G)` first and then `Omega(kappa^j_G)`, without changing the original transpose
or choosing another comparison. For genuine finite normalized Model stages each component
is stable by the already proved single-strength result and stability under parameter looping.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace Quillen.KTheory.Bass.IteratedLoopStrength
open LoopStrength FiniteConeTopology FiniteConeStrength
variable {C : Type u} [Category.{v} C]

/-- The original pointwise strength is natural in the coefficient index. -/
def strengthDiagram (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).obj (F ⋙ parameterLoopingFunctor) ⟶
      (strictDiagramFunctor Q).obj F ⋙ parameterLoopingFunctor where
  app := strength Q F
  naturality {X Y} f := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    apply Path.ext
    funext r
    exact (strictDiagramMapHomotopy_naturality
      (η := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
      (θ := diagramZeroMap (F ⋙ parameterLoopingFunctor) F) (evaluation F)
      (evaluation_naturality F) Q f n r x).symm

/-- Cross the outermost loop first, then loop the previously fixed comparison. -/
def iteratedStrength (Q : C ⥤ Arrow (Arrow C)) :
    ∀ (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}),
      (strictDiagramFunctor Q).obj (loopDiagram j F) ⟶
        loopDiagram j ((strictDiagramFunctor Q).obj F)
  | 0, F => 𝟙 ((strictDiagramFunctor Q).obj F)
  | j + 1, F => strengthDiagram Q (loopDiagram j F) ≫
      Functor.whiskerRight (iteratedStrength Q j F) parameterLoopingFunctor

/-- Each prescribed finite iterated strength is stable on every unlooped Model cone stage. -/
theorem iterated_model_stable (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ)
    (M : C ⥤ Model.{w}) (X : C) :
    IsStableEquivalence
      ((iteratedStrength Q j (iterate Q i (M ⋙ prespectrumFunctor))).app X) := by
  induction j with
  | zero =>
    intro d
    change IsIso ((stableHomotopyFunctor d).map (𝟙 _))
    infer_instance
  | succ j ih =>
    exact (model_strength_stable Q i j M X).comp
      (parameterLoopingMap_isStableEquivalence _ ih)

end Quillen.KTheory.Bass.IteratedLoopStrength
