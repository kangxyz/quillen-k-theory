/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.ConeConeTranspose
public import Quillen.Topology.Prespectrum.PushoutConeInterchange
public import Quillen.Topology.Prespectrum.StableHomotopy

/-!
# Original finite cone-interchange consumers

These clients retain both original cylinder coordinates, independent structure time, literal
quotient inverses and signed stable maps of the actual point-set isomorphisms. No compatibility
of orientation-sensitive iterated boundaries is inferred from the coordinate swap.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace Quillen.Tests.FiniteConeInterchange

/-- The cone/cone transpose preserves structure time while swapping precisely the two cone times.
-/
theorem original_cone_transpose_three_parameters {E F G H : LoopPrespectrum.{u}}
    (f : E ⟶ F) (g : G ⟶ H) (a : E ⟶ G) (b : F ⟶ H) (h : a ≫ g = f ≫ b)
    (n : ℕ) (r s t : unitInterval) (x : E.space n) :
    (ConeConeTranspose.hom f g a b h).map (n + 1)
      ((mappingCone (ConeConeTranspose.horizontal f g a b h)).structureMap n
        (ReducedMappingCone.cylinder ((mappingCone f).point n) ((mappingCone g).point n)
          ((ConeConeTranspose.horizontal f g a b h).map n)
          (r, ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x))) t) =
      ReducedMappingCone.cylinder ((mappingCone a).point (n + 1)) ((mappingCone b).point (n + 1))
        ((ConeConeTranspose.vertical f g a b h).map (n + 1))
        (s, ReducedMappingCone.cylinder (E.point (n + 1)) (G.point (n + 1)) (a.map (n + 1))
          (r, E.structureMap n x t)) := rfl

/-- The actual transpose is bijective in every negative stable degree without topology premises. -/
theorem original_cone_transpose_negative_bijective {E F G H : LoopPrespectrum.{u}}
    (f : E ⟶ F) (g : G ⟶ H) (a : E ⟶ G) (b : F ⟶ H) (h : a ≫ g = f ≫ b) (r : ℕ) :
    Function.Bijective ((stableHomotopyFunctor (-(r : ℤ) - 1)).map
      (ConeConeTranspose.iso f g a b h).hom) :=
  ConcreteCategory.bijective_of_isIso _

/-- Actual cone and span coordinates remain independent of the original structure-loop time. -/
theorem original_span_cone_three_parameters {A B C : Arrow LoopPrespectrum.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (n : ℕ) (r s t : unitInterval) (x : A.left.space n) :
    (HomotopyPushout.coneInterchange f g).map (n + 1)
      ((mappingCone (HomotopyPushout.spanArrowMap f g)).structureMap n
        (ReducedMappingCone.cylinder ((HomotopyPushout.prespectrum f.left g.left).point n)
          ((HomotopyPushout.prespectrum f.right g.right).point n)
          ((HomotopyPushout.spanArrowMap f g).map n)
          (r, HomotopyPushout.cylinder f.left g.left n (s, x))) t) =
      HomotopyPushout.cylinder (mappingConeMap f) (mappingConeMap g) (n + 1)
        (s, ReducedMappingCone.cylinder (A.left.point (n + 1)) (A.right.point (n + 1))
          (A.hom.map (n + 1)) (r, A.left.structureMap n x t)) := rfl

/-- The quotient inverse returns every original point of the actual row-map cone. -/
theorem original_span_cone_inverse {A B C : Arrow LoopPrespectrum.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (n : ℕ)
    (x : (mappingCone (HomotopyPushout.spanArrowMap f g)).space n) :
    (HomotopyPushout.coneInterchangeInv f g).map n
      ((HomotopyPushout.coneInterchange f g).map n x) = x :=
  congrArg (fun m ↦ m.map n x) (HomotopyPushout.coneInterchange_hom_inv f g)

/-- Original right target elements retain their literal right-cone inclusion. -/
theorem original_right_target {A B C : Arrow LoopPrespectrum.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (n : ℕ) (x : C.right.space n) :
    (HomotopyPushout.coneInterchange f g).map n
      ((mappingConeInclusion (HomotopyPushout.spanArrowMap f g)).map n
        ((HomotopyPushout.inr f.right g.right).map n x)) =
      (HomotopyPushout.inr (mappingConeMap f) (mappingConeMap g)).map n
        ((mappingConeInclusion C.hom).map n x) := rfl

end Quillen.Tests.FiniteConeInterchange
