/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ModelZeroNormalization
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexWeakTriangleSquare
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramZeroNull
public import Quillen.Topology.Prespectrum.FiberHomotopySquare

/-!
# Whole selected-zero null squares under actual normalization isomorphisms

The two specified weak-zero transformations give a genuine commuting weak triangle through
zero-source uniqueness. Its realization retains the complete original reversed nulls, the
actual normalization edge, and the constant zero edge, including all old loop coordinates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.ModelZeroNormalization
open Quillen.LoopPrespectrum
variable {V W U T : Model.{u}} (F : V ⟶ W) (G : U ⟶ T)
  (a : V ⟶ U) (b : W ⟶ T)
  (α : (F ≫ b).functor ≅ (a ≫ G).functor)
  (η : (zeroHom V W).functor ⟶ F.functor)
  (θ : (zeroHom U T).functor ⟶ G.functor)
  (hη : ∀ X, W.waldhausen.weq (η.app X))
  (hθ : ∀ X, T.waldhausen.weq (θ.app X))

/-- The specified reversed zero transformation, with only its terminal map retyped. -/
def nullHomotopy {V W : Model.{u}} (F : V ⟶ W)
    (η : (zeroHom V W).functor ⟶ F.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X)) :
    LoopPrespectrum.Homotopy (prespectrumMap F)
      (LoopPrespectrum.zeroHom (prespectrum V) (prespectrum W)) :=
  (prespectrumTransformationHomotopy η hη).symm.cast rfl (prespectrumMap_zeroHom V W)

/-- The old null after the original target evaluation, with no pause or clock change. -/
def postNull : LoopPrespectrum.Homotopy (prespectrumMap F ≫ prespectrumMap b)
    (LoopPrespectrum.zeroHom (prespectrum V) (prespectrum T)) :=
  ((nullHomotopy F η hη).postcomp (prespectrumMap b)).cast rfl (LoopPrespectrum.zeroHom_comp _)

/-- The raw null after the original source evaluation, at the identical reversed time. -/
def preNull : LoopPrespectrum.Homotopy (prespectrumMap a ≫ prespectrumMap G)
    (LoopPrespectrum.zeroHom (prespectrum V) (prespectrum T)) :=
  (LoopPrespectrum.Homotopy.precomp (prespectrumMap a) (nullHomotopy G θ hθ)).cast
    rfl (LoopPrespectrum.comp_zeroHom _)

/-- The actual normalization isomorphism, with the original composite prespectrum endpoints. -/
def comparisonTrack :
    LoopPrespectrum.Homotopy (prespectrumMap F ≫ prespectrumMap b)
      (prespectrumMap a ≫ prespectrumMap G) :=
  (prespectrumTransformationHomotopy α.hom
    (fun _ ↦ T.waldhausen.weq_iso _ inferInstance)).cast
      (prespectrumFunctor.map_comp F b) (prespectrumFunctor.map_comp a G)

/-- The selected weak triangle retains both original zero-source transports. -/
def normalizationSimplex : ModelSimplex V T 2 :=
  ModelSimplex.triangle (postZero η b) α.hom (postZero_weak η hη b)
    (fun _ ↦ T.waldhausen.weq_iso _ inferInstance)

/-- All four original tracks bound the realized actual weak triangle. -/
def normalizationSquare :
    (postNull F b η hη).Square (preNull G a θ hθ)
      (comparisonTrack F G a b α)
      (LoopPrespectrum.Homotopy.refl
        (LoopPrespectrum.zeroHom (prespectrum V) (prespectrum T))) := by
  let S := WeakTriangleSquare.squareOfComposite (postZero η b) α.hom
    (postZero_weak η hη b) (fun _ ↦ T.waldhausen.weq_iso _ inferInstance)
    (preZero θ a) (preZero_weak θ hθ a) (triangle_eq η θ a b α)
  exact {
    level := S.level
    at_zero n s x := (S.at_zero n s x).trans
      (congrArg (fun H ↦ H (unitInterval.symm s, x)) (postZero_level η hη b n))
    at_one n s x := (S.at_one n s x).trans
      (congrArg (fun H ↦ H (unitInterval.symm s, x)) (preZero_level θ hθ a n))
    left n r x := S.left n r x
    right n r x := (S.right n r x).trans
      (congrArg (fun f ↦ f.map n x) (prespectrumMap_zeroHom V T))
    at_point := S.at_point
    comm := S.comm }

/-- No parameter is changed by the original post/precomposition endpoint transports. -/
theorem normalizationSquare_apply (n : ℕ) (r s : unitInterval)
    (x : (prespectrum V).space n) :
    (normalizationSquare F G a b α η θ hη hθ).level n (r, (s, x)) =
      prespectrumSimplexFamily (normalizationSimplex F G a b α η hη) n
        (WeakTriangleSquare.parameter (r, s), x) :=
  WeakTriangleSquare.squareOfComposite_apply (postZero η b) α.hom (postZero_weak η hη b)
    (fun _ ↦ T.waldhausen.weq_iso _ inferInstance) (preZero θ a) (preZero_weak θ hθ a)
    (triangle_eq η θ a b α) n r s x

end Quillen.Waldhausen.IteratedS.ModelZeroNormalization
