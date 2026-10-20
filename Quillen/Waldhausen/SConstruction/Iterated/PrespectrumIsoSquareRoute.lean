/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumCompositionHomotopy
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopyNaturality
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevelsEvaluation

/-!
# Original realization of a pasted Model isomorphism square

The single track of the pasted square is relatively homotopic to the original
precomposed second track followed by the postcomposed first track. The two halves
retain their specified clock. Only exact Model maps and the two actual square
isomorphisms are inputs; no normalization is repeated. The selected whole relative
family is the original transformation-composition triangle at every spectrum level.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Quillen.LoopPrespectrum
universe u
namespace Quillen.Waldhausen.IteratedS.IsoSquareRoute
variable {V₀ V₁ V₂ W₀ W₁ W₂ : Model.{u}}
  (a : V₀ ⟶ V₁) (b : V₁ ⟶ V₂) (N : W₀ ⟶ W₁) (M : W₁ ⟶ W₂)
  (E₀ : V₀ ⟶ W₀) (E₁ : V₁ ⟶ W₁) (E₂ : V₂ ⟶ W₂)
  (s : (a ≫ E₁).functor ≅ (E₀ ≫ N).functor)
  (t : (b ≫ E₂).functor ≅ (E₁ ≫ M).functor)

/-- The first unchanged natural transformation is the original prewhiskered second edge. -/
def leftTransformation : ((a ≫ b) ≫ E₂).functor ⟶ ((a ≫ E₁) ≫ M).functor :=
  whiskerLeft a.functor t.hom

/-- The second unchanged transformation is the original postwhiskered first edge. -/
def rightTransformation : ((a ≫ E₁) ≫ M).functor ⟶ (E₀ ≫ (N ≫ M)).functor :=
  whiskerRight s.hom M.functor

/-- The original prewhiskered isomorphism has weak components without unfolding a consumer. -/
theorem leftTransformation_weak (X : V₀) :
    W₂.waldhausen.weq ((leftTransformation a b M E₁ E₂ t).app X) := by
  change W₂.waldhausen.weq (t.hom.app (a.functor.obj X))
  exact W₂.waldhausen.weq_iso _ inferInstance

/-- Exact postcomposition preserves the weak components of the original first edge. -/
theorem rightTransformation_weak (X : V₀) :
    W₂.waldhausen.weq ((rightTransformation a N M E₀ E₁ s).app X) := by
  change W₂.waldhausen.weq (M.functor.map (s.hom.app X))
  exact M.exact.weak _ (W₁.waldhausen.weq_iso _ inferInstance)

/-- The original functor associators have identity components in the actual pasted route. -/
theorem route_hom :
    (isoSquareRoute s t).hom =
      leftTransformation a b M E₁ E₂ t ≫ rightTransformation a N M E₀ E₁ s := by
  ext X
  simp [isoSquareRoute, leftTransformation, rightTransformation]

/-- The original single realization of the two-square pasted isomorphism. -/
def singleTrack : Homotopy (prespectrumMap ((a ≫ b) ≫ E₂))
    (prespectrumMap (E₀ ≫ (N ≫ M))) :=
  prespectrumTransformationHomotopy (isoSquareRoute s t).hom
    (fun _ ↦ W₂.waldhausen.weq_iso _ inferInstance)

/-- The first half is the original second edge at the original precomposed input. -/
def leftTrack : Homotopy (prespectrumMap ((a ≫ b) ≫ E₂))
    (prespectrumMap ((a ≫ E₁) ≫ M)) :=
  (Homotopy.precomp (prespectrumMap a)
    (prespectrumTransformationHomotopy t.hom
      (fun _ ↦ W₂.waldhausen.weq_iso _ inferInstance))).cast
    ((prespectrumFunctor.map_comp a (b ≫ E₂)).symm.trans
      (congrArg prespectrumMap (Category.assoc a b E₂).symm))
    ((prespectrumFunctor.map_comp a (E₁ ≫ M)).symm.trans
      (congrArg prespectrumMap (Category.assoc a E₁ M).symm))

/-- The second half is the original first edge followed by the original target map. -/
def rightTrack : Homotopy (prespectrumMap ((a ≫ E₁) ≫ M))
    (prespectrumMap (E₀ ≫ (N ≫ M))) :=
  ((prespectrumTransformationHomotopy s.hom
    (fun _ ↦ W₁.waldhausen.weq_iso _ inferInstance)).postcomp (prespectrumMap M)).cast
    (prespectrumFunctor.map_comp (a ≫ E₁) M).symm
    ((prespectrumFunctor.map_comp (E₀ ≫ N) M).symm.trans
      (congrArg prespectrumMap (Category.assoc E₀ N M)))

/-- The complete specified two-edge route, with its literal binary half-clock. -/
def word : Homotopy (prespectrumMap ((a ≫ b) ≫ E₂))
    (prespectrumMap (E₀ ≫ (N ≫ M))) :=
  (leftTrack a b M E₁ E₂ t).trans (rightTrack a N M E₀ E₁ s)

/-- The actual original composition triangle before whole-level endpoint identification. -/
def triangle :=
  prespectrumTransformationCompositionHomotopy
    (leftTransformation a b M E₁ E₂ t) (rightTransformation a N M E₀ E₁ s)
    (leftTransformation_weak a b M E₁ E₂ t)
    (rightTransformation_weak a N M E₀ E₁ s)

/-- No part of the original prewhiskered track changes during its endpoint casts. -/
theorem leftTrack_level (n : ℕ) :
    (leftTrack a b M E₁ E₂ t).level n =
      (prespectrumTransformationHomotopy (leftTransformation a b M E₁ E₂ t)
        (leftTransformation_weak a b M E₁ E₂ t)).level n :=
  (prespectrumTransformationHomotopy_precomp_level t.hom
    (fun _ ↦ W₂.waldhausen.weq_iso _ inferInstance) a n).symm

/-- No part of the original postwhiskered track changes during its endpoint casts. -/
theorem rightTrack_level (n : ℕ) :
    (rightTrack a N M E₀ E₁ s).level n =
      (prespectrumTransformationHomotopy (rightTransformation a N M E₀ E₁ s)
        (rightTransformation_weak a N M E₀ E₁ s)).level n :=
  (prespectrumTransformationHomotopy_postcomp_level s.hom
    (fun _ ↦ W₁.waldhausen.weq_iso _ inferInstance) M n).symm

/-- The pasted isomorphism track is compared to the original two-track word, relative endpoints. -/
def comparison : (singleTrack a b N M E₀ E₁ E₂ s t).RelHomotopy
    (word a b N M E₀ E₁ E₂ s t) :=
  (triangle a b N M E₀ E₁ E₂ s t).ofLevels _ _
    (fun _ ↦ by simp only [singleTrack, route_hom])
    (fun n ↦ Homotopy.trans_level_congr _ _ _ _ n
      (leftTrack_level a b M E₁ E₂ t n) (rightTrack_level a N M E₀ E₁ s n))

/-- The whole selected comparison is the original composition triangle with all times retained. -/
theorem comparison_whole_level (n : ℕ) :
    ((comparison a b N M E₀ E₁ E₂ s t).level n).toContinuousMap =
      ((triangle a b N M E₀ E₁ E₂ s t).level n).toContinuousMap :=
  Homotopy.RelHomotopy.ofLevels_whole_level (triangle a b N M E₀ E₁ E₂ s t) _ _ _ _ n

end Quillen.Waldhausen.IteratedS.IsoSquareRoute
