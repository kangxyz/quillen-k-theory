/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.LocalBases
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteType
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Isomorphism
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Projective
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Flat.Locality
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.GeneralPushforward

/-!
# Finite flat direct image of finite locally free sheaves

A finite flat morphism to a locally noetherian target preserves finite local freeness. The actual direct image restricts to an additive exact vector-bundle functor.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.ExactCategory

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] [Flat f]

/-- The unchanged finite flat affine direct image preserves actual finite local bases.
No noetherianity of the source is assumed separately. -/

theorem finiteLocallyFree_pushforward_affine {R S : CommRingCat.{u}} [IsNoetherianRing R]
    (φ : R ⟶ S) (hφ : φ.hom.Finite) (hflat : φ.hom.Flat)
    (M : (Spec S).Modules) [IsFiniteLocallyFree (Spec S) M] :
    IsFiniteLocallyFree (Spec R) ((Scheme.Modules.pushforward (Spec.map φ)).obj M) := by
  let N := moduleSpecΓFunctor.obj M
  have : Module.Finite S N := finite_globalSections_of_finiteLocallyFree S M
  have : Module.Projective S N := projective_globalSections_of_finiteLocallyFree S M
  let P := (ModuleCat.restrictScalars φ.hom).obj N
  have : Module.Finite R P :=
    ((ModuleCat.FiniteRestrictionScalars.moduleRestriction φ hφ).obj
      ⟨N, (show Module.Finite S N from inferInstance)⟩).property
  have : Module.Flat R P := flat_restrictScalars φ.hom hflat N
  have : Module.FinitePresentation R P := Module.finitePresentation_of_finite R P
  have : Module.Projective R P := Module.Flat.projective_of_finitePresentation
  have : IsFiniteLocallyFree (Spec R) (tilde P) :=
    finiteLocallyFree_tilde_of_finite_projective R P
  let e : tilde P ≅ (Scheme.Modules.pushforward (Spec.map φ)).obj M :=
    ((AlgebraicGeometry.Scheme.Modules.tildePushforwardIso φ).app N).symm ≪≫
      (Scheme.Modules.pushforward (Spec.map φ)).mapIso (asIso M.fromTildeΓ)
  exact finiteLocallyFree_of_iso e

/-- Finite flat direct image to an affine target, with arbitrary source scheme. -/

theorem finiteLocallyFree_pushforward_affine_target {Z : Scheme.{u}}
    (R : CommRingCat.{u}) [IsNoetherianRing R] (f : Z ⟶ Spec R)
    [AlgebraicGeometry.IsFinite f] [Flat f] (M : Z.Modules) [IsFiniteLocallyFree Z M] :
    IsFiniteLocallyFree (Spec R) ((Scheme.Modules.pushforward f).obj M) := by
  obtain ⟨S, φ, hφ, e, hf⟩ :=
    AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.exists_affine_presentation R f
  have hφflat : φ.hom.Flat := by
    have h : Spec.map φ = e.inv ≫ f := by
      rw [hf, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have : Flat (Spec.map φ) := by rw [h]; infer_instance
    exact Flat.SpecMap_iff.mp this
  have : IsFiniteLocallyFree (Spec S) ((Scheme.Modules.restrictFunctor e.inv).obj M) :=
    finiteLocallyFree_restrict e.inv M
  have : IsFiniteLocallyFree (Spec S) ((Scheme.Modules.pushforward e.hom).obj M) :=
    finiteLocallyFree_of_iso ((pushforwardIsoRestrict e).app M).symm
  have : IsFiniteLocallyFree (Spec R)
      ((Scheme.Modules.pushforward (Spec.map φ)).obj ((Scheme.Modules.pushforward e.hom).obj M)) :=
    finiteLocallyFree_pushforward_affine φ hφ hφflat _
  rw [hf]
  exact @finiteLocallyFree_of_iso _ _ _
    ((Scheme.Modules.pushforwardComp e.hom (Spec.map φ)).app M) this

/-- Actual finite flat direct image preserves finite local freeness over a locally
noetherian target, by original open base change and affine target charts. -/

theorem finiteLocallyFree_pushforward {Z X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] [Flat f]
    (M : Z.Modules) [IsFiniteLocallyFree Z M] :
    IsFiniteLocallyFree X ((Scheme.Modules.pushforward f).obj M) := by
  let U := X.affineOpenCover
  apply finiteLocallyFree_of_affineCharts _ U.X U.f (fun x ↦ ⟨U.idx x, U.covers x⟩)
  intro i
  have : IsNoetherianRing (U.X i) :=
    AlgebraicGeometry.Scheme.Modules.Coherent.noetherian_affineChart _ (U.f i)
  have : IsFiniteLocallyFree (CategoryTheory.Limits.pullback f (U.f i))
      ((Scheme.Modules.restrictFunctor (pullback.fst f (U.f i))).obj M) :=
    finiteLocallyFree_restrict _ M
  have : IsFiniteLocallyFree (Spec (U.X i))
      ((Scheme.Modules.pushforward (pullback.snd f (U.f i))).obj
        ((Scheme.Modules.restrictFunctor (pullback.fst f (U.f i))).obj M)) :=
    finiteLocallyFree_pushforward_affine_target _ (pullback.snd f (U.f i)) _
  exact @finiteLocallyFree_of_iso _ _ _
    ((AlgebraicGeometry.Scheme.Modules.openBaseChange f (U.f i)).app M).symm this

/-- The literal original sheaf pushforward restricted to vector bundles. -/

def vectorBundlePushforward : FiniteLocallyFree Z ⥤ FiniteLocallyFree X :=
  ObjectProperty.lift _ ((finiteLocallyFree Z).ι ⋙ Scheme.Modules.pushforward f)
    (fun M ↦ finiteLocallyFree_pushforward f M.obj)

instance vectorBundlePushforward_additive : (vectorBundlePushforward f).Additive where
  map_add := by
    intro M N a b
    apply ObjectProperty.hom_ext
    exact (Scheme.Modules.pushforward f).map_add

/-- The original finite flat vector-bundle direct image is exact. -/

def vectorBundlePushforwardExact :
    ExactFunctor (vectorBundleExactStructure Z) (vectorBundleExactStructure X) where
  toFunctor := vectorBundlePushforward f
  map_conflation S hS := by
    apply (vectorBundleToCoherent_shortExact_iff X _).mpr
    exact ((vectorBundleToCoherent_shortExact_iff Z S).mp hS).map_of_exact
      (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforward f)

end AlgebraicGeometry.Scheme.Modules
