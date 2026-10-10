/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.GlobalLocalizationSupport
public import Quillen.AlgebraicGeometry.Scheme.Coherent.GlobalLocalizationQuotient
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.ObjectExtension
public import Quillen.GTheory.SmallModelLocalization

/-!
# Open localization for the public global scheme G-theory

The actual restriction of global coherent sheaves is a proved Serre
localization on a noetherian ambient scheme. Applying the
small-model theorem in universe `u+1` gives the connective localization
sequence for the public `G` and `SupportedG` definitions. The map from the
ambient scheme to the open is exactly the canonical `restrictionGMap`.

The support maps use the proved exact comparison with the actual coherent
support category. No equality between different-universe realizations is
needed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

private theorem global_exact_transport
    {A B C A' B' C' : Type w}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    (i : A →* B) (f : B →* C) (i' : A' →* B') (f' : B' →* C')
    (eA : A ≃* A') (eB : B ≃* B') (eC : C ≃* C')
    (hi : ∀ a, eB (i a) = i' (eA a))
    (hf : ∀ b, eC (f b) = f' (eB b))
    (h : i'.range = f'.ker) : i.range = f.ker := by
  ext b
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨a, rfl⟩
    apply eC.injective
    rw [map_one, hf, hi]
    have hx : i' (eA a) ∈ i'.range := ⟨eA a, rfl⟩
    rw [h] at hx
    exact hx
  · intro hb
    have hx : eB b ∈ i'.range := by
      rw [h]
      change f' (eB b) = 1
      rw [← hf, hb, map_one]
    obtain ⟨a, ha⟩ := hx
    refine ⟨eA.symm a, eB.injective ?_⟩
    rw [hi, eA.apply_symm_apply, ha]

variable {U X : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual supported quotient is essentially surjective by coherent
object extension from the open. -/
instance quotientCoherentRestriction_essSurj :
    (quotientCoherentRestriction j).EssSurj :=
  quotientCoherentRestriction_essSurj_of_restriction j

/-- The canonical functor from the actual coherent support quotient to the
open is an equivalence, by proved fullness, faithfulness and extension. -/
instance quotientCoherentRestriction_isEquivalence :
    (quotientCoherentRestriction j).IsEquivalence :=
  quotientCoherentRestriction_isEquivalence_of_essSurj j

/-- The actual geometric equivalence between the supported Serre quotient
and coherent sheaves on the open. -/
def coherentSupportQuotientEquivalence : CoherentSupportQuotient j ≌ FiniteTypeSheaves U :=
  (quotientCoherentRestriction j).asEquivalence

/-- Actual restriction of coherent sheaves is the Serre localization by
sheaves whose ordinary stalk support lies outside the open. -/
instance finiteTypeSheavesRestriction_isLocalization :
    (finiteTypeSheavesRestriction j).IsLocalization (finiteTypeSheavesSupportedAway j).isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_of_essSurj j

/-- The same actual geometric localization, expressed by its kernel. -/
instance finiteTypeSheavesRestriction_isLocalization_kernel :
    (finiteTypeSheavesRestriction j).IsLocalization (finiteTypeSheavesRestriction j).kernel.isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_kernel_of_essSurj j

local instance : PreservesFiniteLimits (coherentRestrictionExact j).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits j

local instance : PreservesFiniteColimits (coherentRestrictionExact j).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits j

local instance : (coherentRestrictionExact j).toFunctor.IsLocalization
    (coherentRestrictionExact j).toFunctor.kernel.isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_kernel j

/-- The supported inclusion for the actual public global supported G-group,
using its canonical exact-presentation comparison. -/
def globalInclusionGMap (n : ℕ) :
    SupportedG j n →* G X n :=
  (SmallModelGLocalization.inclusionKMap.{u+1} (coherentRestrictionExact j) n).comp
    (coherentGlobalSupportedGEquiv j n).toMonoidHom

/-- The supported arrow in global localization is exactly the canonical
small-model K-map of the actual supported-coherent inclusion. -/
theorem globalInclusionGMap_eq_smallKMap (n : ℕ) :
    globalInclusionGMap j n = (supportedCoherentInclusionExact j).smallKMap n := by
  have h :
      (SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves X) n).toMonoidHom.comp
          ((supportedCoherentInclusionExact j).smallKMap n) =
        (Devissage.KMap (coherentGlobalSmallSupport j) n).comp
          (coherentGlobalSupportedGEquiv j n).toMonoidHom := by
    change ((SmallModelLocalization.standardExactFunctor.{u+1} (FiniteTypeSheaves X)).KMap n).comp
        ((supportedCoherentInclusionExact j).smallModel.KMap n) =
      ((Devissage.exactInclusion (coherentGlobalSmallSupport j)).KMap n).comp
        ((coherentGlobalSupportComparison j).KMap n)
    rw [← ExactFunctor.KMap_comp, ← ExactFunctor.KMap_comp,
      coherentGlobalSupportComparison_comp_inclusion]
  ext x
  apply (SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves X) n).injective
  calc
    SmallModelLocalization.standardKEquiv (FiniteTypeSheaves X) n (globalInclusionGMap j n x) =
        Devissage.KMap (coherentGlobalSmallSupport j) n
          (coherentGlobalSupportedGEquiv j n x) :=
      (SmallModelLocalization.standardKEquiv (FiniteTypeSheaves X) n).apply_symm_apply _
    _ = SmallModelLocalization.standardKEquiv (FiniteTypeSheaves X) n
        ((supportedCoherentInclusionExact j).smallKMap n x) :=
      (DFunLike.congr_fun h x).symm

/-- The connecting homomorphism into the actual public supported G-group. -/
def globalConnectingHom (n : ℕ) :
    G U (n + 1) →*
      SupportedG j n :=
  (coherentGlobalSupportedGEquiv j n).symm.toMonoidHom.comp
    (SmallModelGLocalization.connectingHom.{u+1} (coherentRestrictionExact j) n)

/-- Exactness at the public global G-group of the ambient scheme. -/
theorem global_inclusion_range_eq_restriction_ker (n : ℕ) :
    (globalInclusionGMap j n).range =
      (restrictionGMap j n).ker := by
  apply global_exact_transport
    (globalInclusionGMap j n) (restrictionGMap j n)
    (SmallModelGLocalization.inclusionKMap.{u+1} (coherentRestrictionExact j) n)
    (ExactFunctor.smallKMap.{u+1} (coherentRestrictionExact j) n)
    (coherentGlobalSupportedGEquiv j n) (MulEquiv.refl _) (MulEquiv.refl _)
  · intro a; rfl
  · intro b; rfl
  · exact SmallModelGLocalization.inclusion_range_eq_KMap_ker.{u+1}
      (coherentRestrictionExact j) n

/-- Exactness at the public global G-group of the selected open. -/
theorem global_restriction_range_eq_connecting_ker (n : ℕ) :
    (restrictionGMap j (n + 1)).range =
      (globalConnectingHom j n).ker := by
  apply global_exact_transport
    (restrictionGMap j (n + 1)) (globalConnectingHom j n)
    (ExactFunctor.smallKMap.{u+1} (coherentRestrictionExact j) (n + 1))
    (SmallModelGLocalization.connectingHom.{u+1} (coherentRestrictionExact j) n)
    (MulEquiv.refl _) (MulEquiv.refl _) (coherentGlobalSupportedGEquiv j n)
  · intro a; rfl
  · intro b
    exact (coherentGlobalSupportedGEquiv j n).apply_symm_apply _
  · exact SmallModelGLocalization.KMap_range_eq_connecting_ker.{u+1}
      (coherentRestrictionExact j) n

/-- Exactness at the actual supported global G-group. -/
theorem global_connecting_range_eq_inclusion_ker (n : ℕ) :
    (globalConnectingHom j n).range =
      (globalInclusionGMap j n).ker := by
  apply global_exact_transport
    (globalConnectingHom j n) (globalInclusionGMap j n)
    (SmallModelGLocalization.connectingHom.{u+1} (coherentRestrictionExact j) n)
    (SmallModelGLocalization.inclusionKMap.{u+1} (coherentRestrictionExact j) n)
    (MulEquiv.refl _) (coherentGlobalSupportedGEquiv j n) (MulEquiv.refl _)
  · intro a
    exact (coherentGlobalSupportedGEquiv j n).apply_symm_apply _
  · intro b; rfl
  · exact SmallModelGLocalization.connecting_range_eq_inclusion_ker.{u+1}
      (coherentRestrictionExact j) n

/-- The public global G-zero restriction map is surjective. -/
theorem global_GZero_surjective :
    Function.Surjective (restrictionGMap j 0) :=
  SmallModelGLocalization.KZero_surjective.{u+1} (coherentRestrictionExact j)

/-- The complete open-immersion connective localization sequence for the
public global scheme G-groups and actual supported coherent sheaves. -/
theorem global_localization_longExact :
    (∀ n, (globalInclusionGMap j n).range =
      (restrictionGMap j n).ker) ∧
    (∀ n, (restrictionGMap j (n + 1)).range =
      (globalConnectingHom j n).ker) ∧
    (∀ n, (globalConnectingHom j n).range =
      (globalInclusionGMap j n).ker) ∧
    Function.Surjective (restrictionGMap j 0) :=
  ⟨global_inclusion_range_eq_restriction_ker j,
    global_restriction_range_eq_connecting_ker j,
    global_connecting_range_eq_inclusion_ker j,
    global_GZero_surjective j⟩

/-- The full connective sequence with both geometric arrows explicitly
written as the canonical small-model K-maps of actual sheaf functors. -/
theorem global_localization_canonical_longExact :
    (∀ n, ((supportedCoherentInclusionExact j).smallKMap n).range =
      (restrictionGMap j n).ker) ∧
    (∀ n, (restrictionGMap j (n + 1)).range =
      (globalConnectingHom j n).ker) ∧
    (∀ n, (globalConnectingHom j n).range =
      ((supportedCoherentInclusionExact j).smallKMap n).ker) ∧
    Function.Surjective (restrictionGMap j 0) := by
  simpa only [globalInclusionGMap_eq_smallKMap] using global_localization_longExact j

/-- The low-degree public global localization tail. -/
theorem global_localization_GZero_tail :
    (restrictionGMap j 1).range =
      (globalConnectingHom j 0).ker ∧
    (globalConnectingHom j 0).range =
      (globalInclusionGMap j 0).ker ∧
    (globalInclusionGMap j 0).range =
      (restrictionGMap j 0).ker ∧
    Function.Surjective (restrictionGMap j 0) :=
  ⟨global_restriction_range_eq_connecting_ker j 0,
    global_connecting_range_eq_inclusion_ker j 0,
    global_inclusion_range_eq_restriction_ker j 0,
    global_GZero_surjective j⟩

end Quillen.CoherentScheme
