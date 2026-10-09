import Quillen.Scheme.Coherent.ClosedImmersion.AffinePushforward
import Quillen.GTheory.FiniteModules.ClosedSupport
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual coherent pushforward from a principal closed subscheme

The functor is the restriction of `Scheme.Modules.pushforward` to the actual
coherent full subcategories. Its global-section comparison is with genuine
quotient-ring restriction of scalars.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme.ClosedImmersion
open FiniteModuleLocalization

variable (R : CommRingCat.{u}) (f : R)

/-- The principal closed subscheme's affine coordinate ring. -/
abbrev principalRing : CommRingCat.{u} := CommRingCat.of (ClosedRing f)

/-- The actual principal closed immersion induced by the quotient map. -/
def principalMap : Spec (principalRing R f) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))

instance principalMap_isClosedImmersion : IsClosedImmersion (principalMap R f) := by
  unfold principalMap
  infer_instance

/-- Actual sheaf pushforward preserves the affine coherence property. -/
theorem affineFiniteSheaf_pushforward {M : (Spec (principalRing R f)).Modules}
    (hM : affineFiniteSheaf (principalRing R f) M) :
    affineFiniteSheaf R ((Scheme.Modules.pushforward (principalMap R f)).obj M) := by
  have : M.IsQuasicoherent := hM.1
  refine ⟨isQuasicoherent_pushforward _ M, ?_⟩
  let N : FGModuleCat (ClosedRing f) := ⟨moduleSpecΓFunctor.obj M, hM.2⟩
  have : Module.Finite R ((moduleSpecΓFunctor ⋙
      ModuleCat.restrictScalars (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))).hom).obj M) :=
    ((closedRestriction f).obj N).property
  exact Module.Finite.equiv
    ((pushforwardGlobalSectionsIso
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))).app M).symm.toLinearEquiv

/-- Actual principal closed pushforward preserves all-affine-chart coherence. -/
theorem coherent_pushforward {M : (Spec (principalRing R f)).Modules}
    (hM : coherent (Spec (principalRing R f)) M) :
    coherent (Spec R) ((Scheme.Modules.pushforward (principalMap R f)).obj M) :=
  (coherent_spec_iff R _).mpr
    (affineFiniteSheaf_pushforward R f ((coherent_spec_iff (principalRing R f) M).mp hM))

variable [IsNoetherianRing R]

/-- Principal closed pushforward on actual coherent sheaves. -/
def coherentPushforward : Coherent (Spec (principalRing R f)) ⥤ Coherent (Spec R) :=
  ObjectProperty.lift _
    (coherentToSheaves (Spec (principalRing R f)) ⋙
      Scheme.Modules.pushforward (principalMap R f))
    (fun M ↦ coherent_pushforward R f M.property)

/-- Forgetting coherence gives the actual sheaf pushforward, definitionally. -/
theorem coherentPushforward_comp_inclusion :
    coherentPushforward R f ⋙ coherentToSheaves (Spec R) =
      coherentToSheaves (Spec (principalRing R f)) ⋙
        Scheme.Modules.pushforward (principalMap R f) := rfl

/-- The actual geometric pushforward/global-sections comparison square. -/
def coherentPushforwardSquare :
    coherentPushforward R f ⋙ (coherentSpecModuleEquivalence R).functor ≅
      (coherentSpecModuleEquivalence (principalRing R f)).functor ⋙ closedRestriction f :=
  ((finiteModule R).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (coherentToSheaves (Spec (principalRing R f)))
      (pushforwardGlobalSectionsIso
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))))

instance coherentPushforward_full : (coherentPushforward R f).Full :=
  Functor.Full.of_comp_faithful_iso (coherentPushforwardSquare R f)

instance coherentPushforward_faithful : (coherentPushforward R f).Faithful :=
  Functor.Faithful.of_comp_iso (coherentPushforwardSquare R f)

instance coherentPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (coherentPushforward R f) := by
  have : PreservesFiniteLimits
      (coherentPushforward R f ⋙ (coherentSpecModuleEquivalence R).functor) :=
    preservesFiniteLimits_of_natIso (coherentPushforwardSquare R f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (coherentPushforward R f)
    (coherentSpecModuleEquivalence R).functor

instance coherentPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (coherentPushforward R f) := by
  have : PreservesFiniteColimits
      (coherentPushforward R f ⋙ (coherentSpecModuleEquivalence R).functor) :=
    preservesFiniteColimits_of_natIso (coherentPushforwardSquare R f).symm
  exact preservesFiniteColimits_of_reflects_of_preserves (coherentPushforward R f)
    (coherentSpecModuleEquivalence R).functor

instance coherentPushforward_additive : (coherentPushforward R f).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (coherentPushforward R f)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The exact functor induced by actual principal closed sheaf pushforward. -/
def coherentPushforwardExact :
    ExactFunctor (coherentExactStructure (Spec (principalRing R f)))
      (coherentExactStructure (Spec R)) where
  toFunctor := coherentPushforward R f
  map_conflation _ h := h.map_of_exact _

end Quillen.CoherentScheme.ClosedImmersion
