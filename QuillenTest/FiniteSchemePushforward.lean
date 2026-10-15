/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.FinitePushforward

/-! Semantic consumers of actual finite coherent direct image. The source's
local noetherianity follows from finiteness and target local noetherianity.
Exactness and affine coordinate comparison concern the original sheaf functor. -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Coherent
universe u
namespace QuillenTest.FiniteSchemePushforward

open Quillen

/-- Finite direct image needs no separately assumed source noetherianity. -/
theorem preservesFiniteColimits_of_target {Z X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] :
    PreservesFiniteColimits (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward f)
      := by
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  infer_instance

/-- The two-copy finite cover is covered, without assuming it is a closed immersion. -/
theorem double_cover_preservesFiniteColimits (X : Scheme.{u}) [IsLocallyNoetherian X] :
    PreservesFiniteColimits (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward
      (coprod.desc (𝟙 X) (𝟙 X))) :=
  preservesFiniteColimits_of_target _

/-- An original exact coherent sequence stays exact under the actual direct image. -/
theorem exact_original_sequence {Z X : Scheme.{u}}
    [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f]
    (S : ShortComplex (FiniteTypeSheaves Z)) (hS : S.Exact) :
    (S.map (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward f)).Exact := hS.map
      _

/-- On affine schemes the original global sections still give finite scalar restriction. -/
def original_affine_globalSections {R S : CommRingCat.{u}}
    [IsNoetherianRing R] [IsNoetherianRing S] (φ : R ⟶ S)
    [AlgebraicGeometry.IsFinite (Spec.map φ)] :
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward (Spec.map φ) ⋙
        (finiteTypeSheavesSpecModuleEquivalence R).functor ≅
      (finiteTypeSheavesSpecModuleEquivalence S).functor ⋙
        ModuleCat.FiniteRestrictionScalars.moduleRestriction φ
          ((AlgebraicGeometry.IsFinite.SpecMap_iff φ).mp inferInstance) :=
  AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine.coherentPushforwardSquare φ _

/-- A split geometric composite gives the corresponding split original G-pushforward. -/
theorem original_split_pushforward {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Y ⟶ X) [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsFinite g]
    (h : f ≫ g = 𝟙 X) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardGMap g n).comp
      (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardGMap f n) =
      MonoidHom.id (G X n) := by
  simp only [←
    AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardGMap_comp, h,
    AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardGMap_id]

end QuillenTest.FiniteSchemePushforward
