/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.GTheory.FiniteModules.RestrictionScalars
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffinePushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.ComparisonGTheory
public import Quillen.CategoryTheory.SmallModel.Functoriality

/-! # The unchanged sheaf direct image along a finite affine map preserves coherence and is exact.
  The public G-map is explicitly formed in the original upper universe, distinct from the
  lower-universe affine model. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.CoherentScheme.FiniteAffine
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Finite)

include hφ in
/-- The actual finite affine direct image preserves the finite-type quasicoherent predicate. -/
theorem affineLocallyFiniteType_pushforward {M : (Spec S).Modules} (hM : affineLocallyFiniteType
  (Spec S) M) :
    affineLocallyFiniteType (Spec R) ((Scheme.Modules.pushforward (Spec.map φ)).obj M) := by
  obtain ⟨hQC, hFG⟩ := (affineLocallyFiniteType_spec_iff S M).mp hM
  let : M.IsQuasicoherent := hQC
  apply (affineLocallyFiniteType_spec_iff R _).mpr
  refine ⟨SchemeSheaf.isQuasicoherent_pushforward φ M, ?_⟩
  let N : FGModuleCat S := ⟨moduleSpecΓFunctor.obj M, hFG⟩
  have : Module.Finite R ((moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).obj M) :=
    ((moduleRestriction φ hφ).obj N).property
  exact Module.Finite.equiv ((SchemeSheaf.pushforwardGlobalSectionsIso φ).app
    M).symm.toLinearEquiv

variable [IsNoetherianRing R] [IsNoetherianRing S]

/-- The literal original sheaf direct image, restricted to coherent objects. -/
def coherentPushforward : FiniteTypeSheaves (Spec S) ⥤ FiniteTypeSheaves (Spec R) :=
  ObjectProperty.lift _
    (finiteTypeSheavesToModules (Spec S) ⋙ Scheme.Modules.pushforward (Spec.map φ))
    (fun M => affineLocallyFiniteType_pushforward φ hφ M.property)

omit [IsNoetherianRing R] [IsNoetherianRing S] in
@[simp] theorem coherentPushforward_comp_inclusion :
    coherentPushforward φ hφ ⋙ finiteTypeSheavesToModules (Spec R) =
      finiteTypeSheavesToModules (Spec S) ⋙ Scheme.Modules.pushforward (Spec.map φ) := rfl

/-- Genuine global sections identify the original direct image with finite scalar restriction. -/
def coherentPushforwardSquare :
    coherentPushforward φ hφ ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor ≅
      (finiteTypeSheavesSpecModuleEquivalence S).functor ⋙ moduleRestriction φ hφ :=
  ((finiteModule R).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules (Spec S))
      (SchemeSheaf.pushforwardGlobalSectionsIso φ))

instance coherentPushforward_preservesFiniteLimits : PreservesFiniteLimits (coherentPushforward φ
  hφ) := by
  have : PreservesFiniteLimits
      (coherentPushforward φ hφ ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor) :=
    preservesFiniteLimits_of_natIso (coherentPushforwardSquare φ hφ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (coherentPushforward φ hφ)
    (finiteTypeSheavesSpecModuleEquivalence R).functor

instance coherentPushforward_preservesFiniteColimits : PreservesFiniteColimits (coherentPushforward
  φ hφ) := by
  have : PreservesFiniteColimits
      (coherentPushforward φ hφ ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor) :=
    preservesFiniteColimits_of_natIso (coherentPushforwardSquare φ hφ).symm
  exact preservesFiniteColimits_of_reflects_of_preserves (coherentPushforward φ hφ)
    (finiteTypeSheavesSpecModuleEquivalence R).functor

instance coherentPushforward_additive : (coherentPushforward φ hφ).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (coherentPushforward φ hφ)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Finite affine pushforward is exact on the unchanged coherent category. -/
def coherentPushforwardExact :
    ExactFunctor (coherentExactStructure (Spec S)) (coherentExactStructure (Spec R)) where
  toFunctor := coherentPushforward φ hφ
  map_conflation _ h := h.map_of_exact _

/-- Covariant finite affine pushforward on the original public scheme G-groups. -/
def pushforwardG (n : ℕ) : G (Spec S) n →* G (Spec R) n :=
  (coherentPushforwardExact φ hφ).smallKMap.{u+1} n

end Quillen.CoherentScheme.FiniteAffine
