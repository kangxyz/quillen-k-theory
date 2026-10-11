/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.ConeFiberComparison
public import Quillen.Topology.Prespectrum.ConeHomotopyExactness

/-!
# Original-map consumers for the cone comparison and universal property

These consumers retain the actual fiber path at independent cone and structure times, compare
that path along an original strict square, and turn nullity in the coherent quotient into a strict
extension realizing every original integer stable map. No stable-excision premise is supplied.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace Quillen.Tests.ConeFiberUniversalProperty

variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The source-to-fiber comparison preserves the original cylinder parameter independently of
prespectrum structure time. -/
theorem original_fiber_path_structure (n : ℕ) (x : E.space n) (s t : unitInterval) :
    ((mappingConeFiberComparison f).map (n + 1) (E.structureMap n x t)).1.2 s =
      (mappingCone f).structureMap n (((mappingConeFiberComparison f).map n x).1.2 s) t := by
  exact congrArg (fun z ↦ z.1.2 s)
    (congrArg (fun p ↦ p t) ((mappingConeFiberComparison f).comm n x))

/-- A strict square keeps the entire path, not only its homotopy class or endpoints. -/
theorem original_square_fiber_path {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B)
    (n : ℕ) (x : A.left.space n) (s : unitInterval) :
    (mappingConeMap sq).map n (((mappingConeFiberComparison A.hom).map n x).1.2 s) =
      ReducedMappingCone.cylinder (B.left.point n) (B.right.point n) (B.hom.map n)
        (s, sq.left.map n x) := by
  exact (congrArg (fun h ↦ (h.map n x).1.2 s)
    (mappingConeFiberComparison_naturality sq)).symm

/-- Nullity in the coherent quotient supplies a strict cone extension whose maps are the
unchanged original stable maps in every integer degree. -/
theorem quotient_nullity_has_original_stable_extension (g : F ⟶ G)
    (hg : coherentHomotopyQuotient.map (f ≫ g) =
      coherentHomotopyQuotient.map (zeroHom E G)) :
    ∃ h : mappingCone f ⟶ G, mappingConeInclusion f ≫ h = g ∧
      ∀ d : ℤ, (stableHomotopyFunctor d).map (mappingConeInclusion f) ≫
        (stableHomotopyFunctor d).map h = (stableHomotopyFunctor d).map g := by
  obtain ⟨h, hh⟩ := (mappingCone_exists_extension_iff f g).mpr
    ((coherentHomotopyQuotient_map_eq_iff _ _).mp hg)
  refine ⟨h, hh, fun d ↦ ?_⟩
  rw [← Functor.map_comp, hh]

/-- The original cone-to-fiber factorization retains the map being studied on every stable group. -/
theorem original_stable_map_factors_through_cone_fiber (d : ℤ) :
    (stableHomotopyFunctor d).map (mappingConeFiberComparison f) ≫
      (stableHomotopyFunctor d).map (homotopyFiberProjection (mappingConeInclusion f)) =
        (stableHomotopyFunctor d).map f := by
  rw [← Functor.map_comp, mappingConeFiberComparison_projection]

/-- The cone of the original zero arrow retracts onto its unchanged target by collapsing the
whole cone cylinder. -/
def zeroArrowConeRetraction (E F : LoopPrespectrum.{u}) : mappingCone (zeroHom E F) ⟶ F :=
  (mappingConeHomEquiv (zeroHom E F)).symm ⟨𝟙 F, by
    simpa only [Category.comp_id] using Homotopy.refl (zeroHom E F)⟩

/-- The zero-arrow extension is a genuine strict retraction of the original inclusion. -/
theorem zero_arrow_cone_retraction (E F : LoopPrespectrum.{u}) :
    mappingConeInclusion (zeroHom E F) ≫ zeroArrowConeRetraction E F = 𝟙 F :=
  mappingConeInclusion_desc _ _ _

/-- Every original cylinder point is collapsed by the zero-arrow retraction. -/
theorem zero_arrow_retraction_cylinder (E F : LoopPrespectrum.{u})
    (n : ℕ) (s : unitInterval) (x : E.space n) :
    (zeroArrowConeRetraction E F).map n
      (ReducedMappingCone.cylinder (E.point n) (F.point n) ((zeroHom E F).map n) (s, x)) =
        F.point n := rfl

end Quillen.Tests.ConeFiberUniversalProperty
