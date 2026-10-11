/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.IdealPushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.AffineSectionsBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction

/-!
# Actual coherent pushforward along arbitrary closed immersions

Open base change and the quotient description of a closed immersion with
affine target prove coherence of the genuine module-sheaf pushforward.
Neither an assumed coherent pushforward nor an assumed localization theorem
is used in this construction.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme.ClosedImmersion.General
open Scheme.Modules

/-- Direct image along a scheme isomorphism is actual restriction along its
inverse. This comparison includes the structure-sheaf module actions. -/
def pushforwardIsoRestrict {Z X : Scheme.{u}} (e : Z ≅ X) :
    pushforward e.hom ≅ restrictFunctor e.inv :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (pushforward e.hom) (restrictFunctorAdjCounitIso e.inv).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (pushforwardComp e.hom e.inv ≪≫ pushforwardCongr e.hom_inv_id ≪≫ pushforwardId Z) _ ≪≫
    Functor.leftUnitor _

/-- Actual pushforward along a scheme isomorphism preserves the all-chart
coherence property. -/
theorem affineLocallyFiniteType_pushforward_iso {Z X : Scheme.{u}} (e : Z ≅ X)
    {M : Z.Modules} (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType X ((pushforward e.hom).obj M) :=
  (affineLocallyFiniteType X).prop_of_iso ((pushforwardIsoRestrict e).app M).symm
    (affineLocallyFiniteType_restrict e.inv hM)

/-- A genuine closed immersion into an affine scheme preserves coherent
module sheaves, by its quotient-ring presentation. -/
theorem affineLocallyFiniteType_pushforward_affine {Z : Scheme.{u}} (R : CommRingCat.{u})
    (i : Z ⟶ Spec R) [IsClosedImmersion i] {M : Z.Modules} (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType (Spec R) ((pushforward i).obj M) := by
  obtain ⟨I, e, hi⟩ := (IsClosedImmersion.Spec_iff (f := i)).mp inferInstance
  rw [hi]
  exact (affineLocallyFiniteType (Spec R)).prop_of_iso
    ((pushforwardComp e.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).app M)
    (Ideal.affineLocallyFiniteType_pushforward R I (affineLocallyFiniteType_pushforward_iso e hM))

/-- Actual direct image along every closed immersion preserves coherence.
The proof tests actual affine charts and uses actual open base change. -/
theorem affineLocallyFiniteType_pushforward {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {M : Z.Modules} (hM : affineLocallyFiniteType Z M) :
    affineLocallyFiniteType X ((pushforward i).obj M) := by
  intro R a _
  have h : affineLocallyFiniteType (Spec R)
      ((pushforward (pullback.snd i a)).obj ((restrictFunctor (pullback.fst i a)).obj M)) :=
    affineLocallyFiniteType_pushforward_affine R (pullback.snd i a)
      (affineLocallyFiniteType_restrict _ hM)
  exact (affineFiniteSheaf R).prop_of_iso ((openBaseChange i a).app M).symm
    ((affineLocallyFiniteType_spec_iff R _).mp h)

/-- Direct image along an embedding of scheme spaces is faithful: every
source open is the preimage of a target open. -/
theorem pushforwardFaithful {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (pushforward i).Faithful where
  map_injective {M N} {f g} h := by
    apply Scheme.Modules.hom_ext
    intro W
    obtain ⟨U, hU, heq⟩ := i.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp W.isOpen
    let V : X.Opens := ⟨U, hU⟩
    have hV : i ⁻¹ᵁ V = W := SetLike.ext' heq
    have h' := congrArg (fun k ↦ Scheme.Modules.Hom.app k V) h
    rw [← hV]
    exact h'

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- Pushforward on actual coherent full subcategories for an arbitrary
closed immersion of locally noetherian schemes. -/
def coherentPushforward : FiniteTypeSheaves Z ⥤ FiniteTypeSheaves X :=
  ObjectProperty.lift _ (finiteTypeSheavesToModules Z ⋙ pushforward i)
    (fun M ↦ affineLocallyFiniteType_pushforward i M.property)

omit [IsLocallyNoetherian Z] [IsLocallyNoetherian X] in
/-- The coherent direct image has exactly the ordinary underlying sheaf
pushforward. -/
theorem coherentPushforward_comp_inclusion :
    coherentPushforward i ⋙ finiteTypeSheavesToModules X =
      finiteTypeSheavesToModules Z ⋙ pushforward i := rfl

instance coherentPushforward_faithful : (coherentPushforward i).Faithful where
  map_injective h := by
    have := pushforwardFaithful i
    apply ObjectProperty.hom_ext
    exact (pushforward i).map_injective (congrArg (fun k ↦ k.hom) h)

instance coherentPushforward_additive : (coherentPushforward i).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact (pushforward i).map_add

instance coherentPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (coherentPushforward i) := by
  have : PreservesFiniteLimits (coherentPushforward i ⋙ finiteTypeSheavesToModules X) := by
    rw [coherentPushforward_comp_inclusion]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (finiteTypeSheavesToModules X)

/-- The geometric open-base-change comparison restricts to the actual
coherent full subcategories. -/
def coherentOpenBaseChange {V : Scheme.{u}}
    (a : V ⟶ X) [IsOpenImmersion a] :
    coherentPushforward i ⋙ finiteTypeSheavesRestriction a ≅
      finiteTypeSheavesRestriction (pullback.fst i a) ⋙ coherentPushforward (pullback.snd i a) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules V)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules Z) (openBaseChange i a))

/-- The actual coherent pushforward into an affine scheme agrees with its
quotient presentation, including the source scheme isomorphism. -/
def affinePresentationComparison {Z : Scheme.{u}}
    (R : CommRingCat.{u}) (i : Z ⟶ Spec R) [IsClosedImmersion i]
    (I : Ideal R) (e : Z ≅ Spec (Ideal.closedRing R I))
    (hi : i = e.hom ≫ Ideal.closedMap R I) :
    coherentPushforward i ≅ finiteTypeSheavesRestriction e.inv ⋙ Ideal.coherentPushforward R I :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules (Spec R))
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules Z)
      (pushforwardCongr hi ≪≫ (pushforwardComp e.hom (Ideal.closedMap R I)).symm ≪≫
        Functor.isoWhiskerRight (pushforwardIsoRestrict e) _))

instance coherentPushforward_affine_preservesFiniteColimits {Z : Scheme.{u}}
    [IsLocallyNoetherian Z] (R : CommRingCat.{u}) [IsNoetherianRing R]
    (i : Z ⟶ Spec R) [IsClosedImmersion i] :
    PreservesFiniteColimits (coherentPushforward i) := by
  obtain ⟨I, e, hi⟩ := (IsClosedImmersion.Spec_iff (f := i)).mp inferInstance
  exact preservesFiniteColimits_of_natIso (affinePresentationComparison R i I e hi).symm

/-- Zero coherent sheaves can be recognized on all actual affine charts. -/
theorem coherent_isZero_of_affineRestrictions {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : FiniteTypeSheaves X)
    (h : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (a : Spec R ⟶ X)
      [IsOpenImmersion a], IsZero ((finiteTypeSheavesRestriction a).obj M)) : IsZero M := by
  apply IsZero.of_full_of_faithful_of_isZero (finiteTypeSheavesToModules X) M
  apply (SchemeSheaf.isZero_iff_stalks M.obj).mpr
  intro x
  obtain ⟨R, a, ha, y, hy⟩ := Scheme.exists_Spec_apply_eq x
  have : IsOpenImmersion a := ha
  have : IsNoetherianRing R := noetherian_affineChart R a
  have h' : IsZero ((restrictFunctor a).obj M.obj) :=
    (finiteTypeSheavesToModules (Spec R)).map_isZero (h R a)
  have hz := (SchemeSheaf.stalkFunctor (Spec R) y).map_isZero h'
  have hz' : IsZero ((SchemeSheaf.stalkFunctor X (a y)).obj M.obj) :=
    hz.of_iso ((restrictStalkNatIso a y).app M.obj).symm
  simpa only [hy] using hz'

/-- Actual closed coherent pushforward preserves epimorphisms. The cokernel
vanishes on every affine chart by the proved affine exactness. -/
instance coherentPushforward_preservesEpimorphisms :
    (coherentPushforward i).PreservesEpimorphisms where
  preserves {M N} f hf := by
    apply Preadditive.epi_of_isZero_cokernel
    apply coherent_isZero_of_affineRestrictions
    intro R _ a _
    have : PreservesFiniteColimits (coherentPushforward i ⋙ finiteTypeSheavesRestriction a) :=
      preservesFiniteColimits_of_natIso (coherentOpenBaseChange i a).symm
    have : Epi ((finiteTypeSheavesRestriction a).map ((coherentPushforward i).map f)) :=
      inferInstanceAs (Epi ((coherentPushforward i ⋙ finiteTypeSheavesRestriction a).map f))
    exact (isZero_cokernel_of_epi
      ((finiteTypeSheavesRestriction a).map ((coherentPushforward i).map f))).of_iso
      (PreservesCokernel.iso (finiteTypeSheavesRestriction a) ((coherentPushforward i).map f))

instance coherentPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (coherentPushforward i) := by
  have : (coherentPushforward i).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- Exact direct image on actual coherent sheaves for an arbitrary closed
immersion of locally noetherian schemes. -/
def coherentPushforwardExact :
    ExactFunctor (coherentExactStructure Z) (coherentExactStructure X) where
  toFunctor := coherentPushforward i
  map_conflation _ h := h.map_of_exact _

/-- The genuine covariant closed-immersion map on public scheme G-theory. -/
def coherentPushforwardGMap (n : ℕ) : G Z n →* G X n :=
  (coherentPushforwardExact i).smallKMap n

/-- The global construction specializes definitionally to the actual
quotient pushforward already constructed in the affine case. -/
@[simp] theorem coherentPushforward_quotient (R : CommRingCat.{u})
    (I : Ideal R) :
    coherentPushforward (Ideal.closedMap R I) = Ideal.coherentPushforward R I := rfl

/-- The global canonical map agrees with the established affine closed map. -/
@[simp] theorem coherentPushforwardGMap_quotient (R : CommRingCat.{u}) [IsNoetherianRing R]
    (I : Ideal R) (n : ℕ) :
    coherentPushforwardGMap (Ideal.closedMap R I) n = Ideal.coherentPushforwardGMap R I n := rfl

/-- Actual open base change commutes with canonical global G-theory maps. -/
theorem coherentPushforwardGMap_openBaseChange {V : Scheme.{u}} [IsLocallyNoetherian V]
    (a : V ⟶ X) [IsOpenImmersion a] (n : ℕ) :
    (restrictionGMap a n).comp (coherentPushforwardGMap i n) =
      (coherentPushforwardGMap (pullback.snd i a) n).comp
        (restrictionGMap (pullback.fst i a) n) := by
  have h := ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := (coherentPushforwardExact i).comp (coherentRestrictionExact a))
    (G := (coherentRestrictionExact (pullback.fst i a)).comp
      (coherentPushforwardExact (pullback.snd i a)))
    (coherentOpenBaseChange i a) n
  simpa only [ExactFunctor.smallKMap_comp, coherentPushforwardGMap, restrictionGMap] using h

end Quillen.CoherentScheme.ClosedImmersion.General
