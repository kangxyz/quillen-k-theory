/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Finite.AffinePushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.AffineDetection
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.OpenBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.PushforwardIso
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Coherent direct image along arbitrary finite morphisms

The original module-sheaf pushforward along a finite morphism preserves
finite-type quasicoherent sheaves. Actual affine presentations and open base
change reduce this to finite restriction of scalars. Over locally noetherian
schemes this gives an exact coherent functor and its original G-theory map.
No proper direct-image or perfect-complex preservation assertion is made.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace Quillen.CoherentScheme.Finite

/-- A finite map into an affine scheme has an actual finite coordinate
presentation, retaining the original scheme map. -/
theorem exists_affine_presentation {Z : Scheme.{u}} (R : CommRingCat.{u})
    (f : Z ⟶ Spec R) [AlgebraicGeometry.IsFinite f] :
    ∃ (S : CommRingCat.{u}) (φ : R ⟶ S), φ.hom.Finite ∧
      ∃ e : Z ≅ Spec S, f = e.hom ≫ Spec.map φ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ f)
  have hf : AlgebraicGeometry.IsFinite (Spec.map φ) := by
    rw [hφ]
    infer_instance
  refine ⟨_, φ, (AlgebraicGeometry.IsFinite.SpecMap_iff φ).mp hf, Z.isoSpec, ?_⟩
  rw [hφ, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Actual direct image to an affine target preserves the finite-type
quasicoherent predicate, using the genuine finite coordinate presentation. -/
theorem affineLocallyFiniteType_pushforward_affine {Z : Scheme.{u}} (R : CommRingCat.{u})
    (f : Z ⟶ Spec R) [AlgebraicGeometry.IsFinite f] {M : Z.Modules}
    (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType (Spec R) ((pushforward f).obj M) := by
  obtain ⟨S, φ, hφ, e, hf⟩ := exists_affine_presentation R f
  rw [hf]
  apply (affineLocallyFiniteType (Spec R)).prop_of_iso ((pushforwardComp e.hom (Spec.map φ)).app M)
  apply FiniteAffine.affineLocallyFiniteType_pushforward φ hφ
  exact (affineLocallyFiniteType (Spec S)).prop_of_iso
    ((SchemeSheaf.pushforwardIsoRestrict e).app M).symm
    (affineLocallyFiniteType_restrict e.inv hM)

/-- Direct image along any finite morphism preserves the actual all-chart
finite-type quasicoherent predicate. No noetherianity is needed here. -/
theorem affineLocallyFiniteType_pushforward {Z X : Scheme.{u}} (f : Z ⟶ X)
    [AlgebraicGeometry.IsFinite f] {M : Z.Modules} (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType X ((pushforward f).obj M) := by
  intro R a _
  have h : affineLocallyFiniteType (Spec R)
      ((pushforward (pullback.snd f a)).obj ((restrictFunctor (pullback.fst f a)).obj M)) :=
    affineLocallyFiniteType_pushforward_affine R (pullback.snd f a)
      (affineLocallyFiniteType_restrict _ hM)
  exact (affineFiniteSheaf R).prop_of_iso ((openBaseChange f a).app M).symm
    ((affineLocallyFiniteType_spec_iff R _).mp h)

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f]

/-- The unchanged sheaf direct image restricted to actual coherent objects. -/
def coherentPushforward : FiniteTypeSheaves Z ⥤ FiniteTypeSheaves X :=
  ObjectProperty.lift _ (finiteTypeSheavesToModules Z ⋙ pushforward f)
    (fun M ↦ affineLocallyFiniteType_pushforward f M.property)

omit [IsLocallyNoetherian Z] [IsLocallyNoetherian X] in
/-- The underlying functor remains the original module-sheaf pushforward. -/
@[simp] theorem coherentPushforward_comp_inclusion :
    coherentPushforward f ⋙ finiteTypeSheavesToModules X =
      finiteTypeSheavesToModules Z ⋙ pushforward f := rfl

instance coherentPushforward_additive : (coherentPushforward f).Additive where
  map_add := by
    intro M N a b
    apply ObjectProperty.hom_ext
    exact (pushforward f).map_add

instance coherentPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (coherentPushforward f) := by
  have : PreservesFiniteLimits (coherentPushforward f ⋙ finiteTypeSheavesToModules X) := by
    rw [coherentPushforward_comp_inclusion]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (finiteTypeSheavesToModules X)

/-- Actual open base change restricts to the original coherent subcategories. -/
def coherentOpenBaseChange {V : Scheme.{u}} (a : V ⟶ X) [IsOpenImmersion a] :
    coherentPushforward f ⋙ finiteTypeSheavesRestriction a ≅
      finiteTypeSheavesRestriction (pullback.fst f a) ⋙ coherentPushforward (pullback.snd f a) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules V)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules Z) (openBaseChange f a))

/-- The finite affine presentation comparison retains the source isomorphism
and the original coordinate-map direct image. -/
def affinePresentationComparison {Z : Scheme.{u}} (R S : CommRingCat.{u})
    (f : Z ⟶ Spec R) [AlgebraicGeometry.IsFinite f] (φ : R ⟶ S) (hφ : φ.hom.Finite)
    (e : Z ≅ Spec S) (hf : f = e.hom ≫ Spec.map φ) :
    coherentPushforward f ≅
      finiteTypeSheavesRestriction e.inv ⋙ FiniteAffine.coherentPushforward φ hφ :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules (Spec R))
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules Z)
      (pushforwardCongr hf ≪≫ (pushforwardComp e.hom (Spec.map φ)).symm ≪≫
        Functor.isoWhiskerRight (SchemeSheaf.pushforwardIsoRestrict e) _))

instance coherentPushforward_affine_preservesFiniteColimits {Z : Scheme.{u}}
    [IsLocallyNoetherian Z] (R : CommRingCat.{u}) [IsNoetherianRing R]
    (f : Z ⟶ Spec R) [AlgebraicGeometry.IsFinite f] :
    PreservesFiniteColimits (coherentPushforward f) := by
  obtain ⟨S, φ, hφ, e, hf⟩ := exists_affine_presentation R f
  have : IsNoetherianRing S := noetherian_affineChart S e.inv
  exact preservesFiniteColimits_of_natIso (affinePresentationComparison R S f φ hφ e hf).symm

/-- The actual finite coherent direct image preserves epimorphisms, detected
by vanishing cokernels on the original affine target charts. -/
instance coherentPushforward_preservesEpimorphisms :
    (coherentPushforward f).PreservesEpimorphisms where
  preserves {M N} a ha := by
    apply Preadditive.epi_of_isZero_cokernel
    apply coherent_isZero_of_affineRestrictions
    intro R _ j _
    have : PreservesFiniteColimits (coherentPushforward f ⋙ finiteTypeSheavesRestriction j) :=
      preservesFiniteColimits_of_natIso (coherentOpenBaseChange f j).symm
    have : Epi ((finiteTypeSheavesRestriction j).map ((coherentPushforward f).map a)) :=
      inferInstanceAs (Epi ((coherentPushforward f ⋙ finiteTypeSheavesRestriction j).map a))
    exact (isZero_cokernel_of_epi
      ((finiteTypeSheavesRestriction j).map ((coherentPushforward f).map a))).of_iso
      (PreservesCokernel.iso (finiteTypeSheavesRestriction j) ((coherentPushforward f).map a))

instance coherentPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (coherentPushforward f) := by
  have : (coherentPushforward f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- Exact direct image on actual coherent sheaves under geometric finiteness. -/
def coherentPushforwardExact :
    ExactFunctor (coherentExactStructure Z) (coherentExactStructure X) where
  toFunctor := coherentPushforward f
  map_conflation _ h := h.map_of_exact _

/-- The canonical covariant G-map of the actual finite coherent direct image. -/
def coherentPushforwardGMap (n : ℕ) : G Z n →* G X n :=
  (coherentPushforwardExact f).smallKMap n

end Quillen.CoherentScheme.Finite
