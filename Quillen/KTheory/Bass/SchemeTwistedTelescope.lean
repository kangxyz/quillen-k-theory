/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeTwistedConjugacy
public import Quillen.KTheory.Bass.SchemeCurrentStageTelescope

/-! # The actual fixed-word conjugacy on normalized telescopes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
open FiniteConeTopology
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The same normalized objects with their prescribed cyclic and insertion-word transitions. -/
def twistedTelescope (A : Track laurent.op coefficient F) :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w} :=
  Telescope.diagramFunctor (fun i => normalized squareFunctor i F) (twistedTransition A)

/-- Actual reversal and accumulated cone words descend to a natural telescope map. -/
def conjugacyTelescopeMap (A : Track laurent.op coefficient F) :
    normalizedTelescope A ⟶ twistedTelescope A :=
  Telescope.diagramMap (fun i => normalized squareFunctor i F)
    (fun i => normalized squareFunctor i F) (normalizedTransition A) (twistedTransition A)
    (fun i => (conjugatingIso i F).hom) (fun i => (twisted_adjacent A i).symm)

/-- The fixed conjugacy preserves every original stage and complete telescope height. -/
theorem conjugacyTelescopeMap_cylinder (A : Track laurent.op coefficient F)
    (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s : unitInterval)
    (x : ((normalized squareFunctor i F).obj X).space n) :
    ((conjugacyTelescopeMap A).app X).map n
      (Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
        (fun j => (normalizedTransition A j).app X) n i (s, x)) =
    Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
      (fun j => (twistedTransition A j).app X) n i
      (s, ((conjugatingIso i F).hom.app X).map n x) :=
  Telescope.diagramMap_cylinder (fun j => normalized squareFunctor j F)
    (fun j => normalized squareFunctor j F) (normalizedTransition A) (twistedTransition A)
    (fun j => (conjugatingIso j F).hom) (fun j => (twisted_adjacent A j).symm) X n i s x

/-- Original finite-stage inclusions commute with the actual fixed-word map. -/
theorem conjugacyTelescopeMap_inclusion (A : Track laurent.op coefficient F) (i : ℕ) :
    Telescope.diagramInclusion (fun j => normalized squareFunctor j F)
        (normalizedTransition A) i ≫ conjugacyTelescopeMap A =
      (conjugatingIso i F).hom ≫
        Telescope.diagramInclusion (fun j => normalized squareFunctor j F)
          (twistedTransition A) i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- On actual Model input each stage is an isomorphism, so the same telescope map is stable. -/
theorem model_conjugacyTelescopeMap_stable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence ((conjugacyTelescopeMap A).app X) := by
  let : ∀ i n, T1Space
      ((normalized squareFunctor i (M ⋙ prespectrumFunctor)).obj X |>.space n) := by
    intro i n
    rw [normalized_obj]
    exact modelLoopsIterateSpaceT1Space squareFunctor i i M X n
  exact Telescope.map_isStableEquivalence
    (fun i => (normalized squareFunctor i (M ⋙ prespectrumFunctor)).obj X)
    (fun i => (normalizedTransition A i).app X)
    (fun i => (normalized squareFunctor i (M ⋙ prespectrumFunctor)).obj X)
    (fun i => (twistedTransition A i).app X)
    (fun i => (conjugatingIso i (M ⋙ prespectrumFunctor)).hom.app X)
    (fun i => congrArg (fun η => η.app X) (twisted_adjacent A i).symm)
    (fun _ _ => by infer_instance)

end Quillen.KTheory.Bass.SchemeNaturalSeed
