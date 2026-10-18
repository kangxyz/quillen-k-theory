/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictLaurentSeed
public import Quillen.Topology.Prespectrum.LoopTranspose
public import Quillen.KTheory.Bass.LoopStrength

/-!
# Parameter looping of the original Laurent seed

A whole coefficient-natural Laurent track acts pointwise on the original based loops.
The associated seed commutes exactly with Bass loop strength. The two loop coordinates
are retained in their original order, including the transpose already present in strength.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open scoped Topology unitInterval
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace Quillen.KTheory.Bass.LaurentSeed
open LoopStrength
variable {R : CommRingCat.{u}} {F : Under R ⥤ LoopPrespectrum.{w}}

/-- Apply the actual Laurent track at every point of the original parameter loop. -/
def Track.loop (A : Track F) : Track (F ⋙ parameterLoopingFunctor) where
  homotopy a := (A.homotopy a).parameterLooping
  naturality g n s γ := by
    apply Path.ext
    funext r
    exact A.naturality g n s (Path.toContinuousMap γ r)

/-- Track time and input-loop time remain independent. -/
theorem Track.loop_apply (A : Track F) (a : Under R) (n : ℕ)
    (s r : unitInterval) (γ : (parameterLooping (F.obj a)).space n) :
    Path.toContinuousMap ((A.loop.homotopy a).level n (s, γ)) r =
      (A.homotopy a).level n (s, Path.toContinuousMap γ r) := rfl

/-- Bass loop strength compares the two actual seeds with their full prescribed null words. -/
theorem Track.seed_loop_strength (A : Track F) (a : Under R) :
    A.loop.seedMap a ≫ strength (laurentUnderSquareFunctor R) F a =
      parameterLoopingMap (A.seedMap a) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext r
  apply Path.ext
  funext t
  let η : (F ⋙ parameterLoopingFunctor) ⟶ F :=
    diagramHomotopyAt
      (η := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
      (θ := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
      (evaluation F) (evaluation_naturality F) r
  have h := Track.seed_square A.loop A η (by
    intro b m s δ
    rfl)
  have hv := congrArg (fun k => Path.toContinuousMap ((k.app a).map n γ) t) h
  change Path.toContinuousMap
    ((bassHomotopy (evaluation F) (evaluation_naturality F)
      (laurentUnderSquareFunctor R) a).level n (r, (A.loop.seedMap a).map n γ)) t =
        Path.toContinuousMap ((A.seedMap a).map n (Path.toContinuousMap γ r)) t
  have hb := bassHomotopy_apply (E := F ⋙ parameterLoopingFunctor) (F := F)
    (evaluation F) (evaluation_naturality F) (laurentUnderSquareFunctor R) a n r
    ((A.loop.seedMap a).map n γ)
  exact (congrArg (fun p => Path.toContinuousMap p t) hb).trans hv

/-- The output order is input-loop time first and original seed time second. -/
theorem Track.seed_loop_strength_apply (A : Track F) (a : Under R) (n : ℕ)
    (γ : (parameterLooping (F.obj a)).space n) (r t : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      (((A.loop.seedMap a ≫ strength (laurentUnderSquareFunctor R) F a).map n γ)) r) t =
        Path.toContinuousMap ((A.seedMap a).map n (Path.toContinuousMap γ r)) t := by
  rw [A.seed_loop_strength]
  rfl

end Quillen.KTheory.Bass.LaurentSeed
