/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.Support

/-!
# Exact restriction and actual support for global coherent sheaves

The affine-chart definition is stable under open restriction by composition
of actual affine charts. The full coherent inclusion reflects finite limits
and colimits, so restriction is exact. Its kernel is exactly vanishing on
the open, equivalently ordinary stalk support in the closed complement.
No global quotient-equivalence or global localization theorem is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

/-- Composition of affine charts proves actual open restriction preserves
the affine-local finite quasicoherent condition. -/
theorem affineLocallyFiniteType_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} (hM : affineLocallyFiniteType X M) :
    affineLocallyFiniteType U ((Scheme.Modules.restrictFunctor j).obj M) := by
  intro R f _
  exact (affineFiniteSheaf R).prop_of_iso ((Scheme.Modules.restrictFunctorComp f j).app M)
    (hM R (f ≫ j))

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Open restriction of affine-locally finite-type sheaves. -/
def finiteTypeSheavesRestriction : FiniteTypeSheaves X ⥤ FiniteTypeSheaves U :=
  (affineLocallyFiniteType U).lift ((affineLocallyFiniteType X).ι ⋙ Scheme.Modules.restrictFunctor
    j)
    (fun M => affineLocallyFiniteType_restrict j M.property)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian U] in
/-- The underlying sheaf functor is literally the actual open restriction. -/
theorem finiteTypeSheavesRestriction_comp_inclusion :
    finiteTypeSheavesRestriction j ⋙ finiteTypeSheavesToModules U =
      finiteTypeSheavesToModules X ⋙ Scheme.Modules.restrictFunctor j := rfl

instance finiteTypeSheavesRestriction_preservesFiniteLimits : PreservesFiniteLimits
  (finiteTypeSheavesRestriction j)
  := by
  have : PreservesFiniteLimits (finiteTypeSheavesRestriction j ⋙ finiteTypeSheavesToModules U) := by
    rw [finiteTypeSheavesRestriction_comp_inclusion]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (finiteTypeSheavesRestriction j)
    (finiteTypeSheavesToModules U)

instance finiteTypeSheavesRestriction_preservesFiniteColimits : PreservesFiniteColimits
  (finiteTypeSheavesRestriction
  j) := by
  have : PreservesFiniteColimits (finiteTypeSheavesRestriction j ⋙ finiteTypeSheavesToModules U) :=
    by
    rw [finiteTypeSheavesRestriction_comp_inclusion]
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (finiteTypeSheavesRestriction j)
    (finiteTypeSheavesToModules
    U)

instance finiteTypeSheavesRestriction_additive : (finiteTypeSheavesRestriction j).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (finiteTypeSheavesRestriction j)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Actual open restriction is an exact functor on coherent sheaves. -/
def coherentRestrictionExact : ExactFunctor (coherentExactStructure X) (coherentExactStructure U)
  where
  toFunctor := finiteTypeSheavesRestriction j
  map_conflation _ h := h.map_of_exact _

/-- Its genuine canonical map on the initially upper-universe global G-groups. -/
def restrictionGMap (n : ℕ) : G X n →* G U n :=
  (coherentRestrictionExact j).smallKMap n

/-- Actual coherent sheaves vanishing on the selected open. -/
def finiteTypeSheavesSupportedAway : ObjectProperty (FiniteTypeSheaves X) :=
  (SchemeSheaf.supportedAway j).inverseImage (finiteTypeSheavesToModules X)

instance finiteTypeSheavesSupportedAway_isSerreClass : (finiteTypeSheavesSupportedAway
  j).IsSerreClass := by
  change ((SchemeSheaf.supportedAway j).inverseImage (finiteTypeSheavesToModules X)).IsSerreClass
  infer_instance

omit [IsLocallyNoetherian X] [IsLocallyNoetherian U] in
/-- This support property is exactly the kernel of actual finite-type sheaf restriction. -/
theorem finiteTypeSheavesRestriction_kernel_eq_support :
    (finiteTypeSheavesRestriction j).kernel = finiteTypeSheavesSupportedAway j := by
  funext M
  apply propext
  change IsZero ((finiteTypeSheavesRestriction j).obj M) ↔
    IsZero ((finiteTypeSheavesToModules U).obj ((finiteTypeSheavesRestriction j).obj M))
  exact ⟨Functor.map_isZero _, fun h => IsZero.of_full_of_faithful_of_isZero _ _ h⟩

omit [IsLocallyNoetherian X] [IsLocallyNoetherian U] in
/-- Support membership has its ordinary stalk-support meaning. -/
theorem finiteTypeSheavesSupportedAway_iff_support_subset (M : FiniteTypeSheaves X) :
    finiteTypeSheavesSupportedAway j M ↔ SchemeSheaf.support M.obj ⊆ (Set.range j)ᶜ := by
  change SchemeSheaf.supportedAway j M.obj ↔ _
  rw [SchemeSheaf.supportedAway_iff_support_disjoint]
  exact Set.disjoint_left

/-- The actual full abelian category of supported coherent sheaves. -/
abbrev SupportedFiniteTypeSheaves := (finiteTypeSheavesSupportedAway j).FullSubcategory

instance instAbelianSupportedCoherent : Abelian (SupportedFiniteTypeSheaves j) := inferInstance
instance supportedCoherent_essentiallySmall : EssentiallySmall.{u+1} (SupportedFiniteTypeSheaves j)
  :=
  inferInstance

/-- The standard exact structure on the actual support category. -/
def supportedCoherentExactStructure : ExactStructure (SupportedFiniteTypeSheaves j) :=
  abelianExactStructure
  _

/-- Upper-universe G-theory with actual coherent support. -/
abbrev SupportedG (n : ℕ) : Type (u+1) :=
  ExactStructure.SmallK.{u+1} (supportedCoherentExactStructure j) n

end Quillen.CoherentScheme
