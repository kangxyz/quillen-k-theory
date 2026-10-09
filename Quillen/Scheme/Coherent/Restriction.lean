import Quillen.Scheme.Coherent.Basic
import Quillen.Scheme.Sheaf.Support

/-!
# Exact restriction and actual support for global coherent sheaves

The affine-chart definition is stable under open restriction by composition
of actual affine charts. The full coherent inclusion reflects finite limits
and colimits, so restriction is exact. Its kernel is exactly vanishing on
the open, equivalently ordinary stalk support in the closed complement.
No global quotient-equivalence or global localization theorem is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

/-- Composition of affine charts proves actual open restriction preserves
the affine-local finite quasicoherent condition. -/
theorem coherent_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} (hM : coherent X M) :
    coherent U ((Scheme.Modules.restrictFunctor j).obj M) := by
  intro R f _
  exact (affineFiniteSheaf R).prop_of_iso ((Scheme.Modules.restrictFunctorComp f j).app M)
    (hM R (f ≫ j))

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual geometric restriction of coherent sheaves. -/
def coherentRestriction : Coherent X ⥤ Coherent U :=
  (coherent U).lift ((coherent X).ι ⋙ Scheme.Modules.restrictFunctor j)
    (fun M => coherent_restrict j M.property)

/-- The underlying sheaf functor is literally the actual open restriction. -/
theorem coherentRestriction_comp_inclusion :
    coherentRestriction j ⋙ coherentToSheaves U =
      coherentToSheaves X ⋙ Scheme.Modules.restrictFunctor j := rfl

instance coherentRestriction_preservesFiniteLimits : PreservesFiniteLimits (coherentRestriction j) := by
  have : PreservesFiniteLimits (coherentRestriction j ⋙ coherentToSheaves U) := by
    rw [coherentRestriction_comp_inclusion]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (coherentRestriction j) (coherentToSheaves U)

instance coherentRestriction_preservesFiniteColimits : PreservesFiniteColimits (coherentRestriction j) := by
  have : PreservesFiniteColimits (coherentRestriction j ⋙ coherentToSheaves U) := by
    rw [coherentRestriction_comp_inclusion]
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (coherentRestriction j) (coherentToSheaves U)

instance coherentRestriction_additive : (coherentRestriction j).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (coherentRestriction j)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Actual open restriction is an exact functor on coherent sheaves. -/
def coherentRestrictionExact : ExactFunctor (coherentExactStructure X) (coherentExactStructure U) where
  toFunctor := coherentRestriction j
  map_conflation _ h := h.map_of_exact _

/-- Its genuine canonical map on the initially upper-universe global G-groups. -/
def restrictionGMap (n : ℕ) : G X n →* G U n :=
  (coherentRestrictionExact j).smallKMap n

/-- Actual coherent sheaves vanishing on the selected open. -/
def coherentSupportedAway : ObjectProperty (Coherent X) :=
  (SchemeSheaf.supportedAway j).inverseImage (coherentToSheaves X)

instance coherentSupportedAway_isSerreClass : (coherentSupportedAway j).IsSerreClass := by
  change ((SchemeSheaf.supportedAway j).inverseImage (coherentToSheaves X)).IsSerreClass
  infer_instance

/-- This support category is exactly the kernel of actual coherent restriction. -/
theorem coherentRestriction_kernel_eq_support :
    (coherentRestriction j).kernel = coherentSupportedAway j := by
  funext M
  apply propext
  change IsZero ((coherentRestriction j).obj M) ↔
    IsZero ((coherentToSheaves U).obj ((coherentRestriction j).obj M))
  exact ⟨Functor.map_isZero _, fun h => IsZero.of_full_of_faithful_of_isZero _ _ h⟩

omit [IsLocallyNoetherian U] in
/-- Support membership has its ordinary stalk-support meaning. -/
theorem coherentSupportedAway_iff_support_subset (M : Coherent X) :
    coherentSupportedAway j M ↔ SchemeSheaf.support M.obj ⊆ (Set.range j)ᶜ := by
  change SchemeSheaf.supportedAway j M.obj ↔ _
  rw [SchemeSheaf.supportedAway_iff_support_disjoint]
  exact Set.disjoint_left

/-- The actual full abelian category of supported coherent sheaves. -/
abbrev SupportedCoherent := (coherentSupportedAway j).FullSubcategory

instance supportedCoherent_abelian : Abelian (SupportedCoherent j) := inferInstance
instance supportedCoherent_essentiallySmall : EssentiallySmall.{u+1} (SupportedCoherent j) := inferInstance

/-- The standard exact structure on the actual support category. -/
def supportedCoherentExactStructure : ExactStructure (SupportedCoherent j) := abelianExactStructure _

/-- Upper-universe G-theory with actual coherent support. -/
abbrev SupportedG (n : ℕ) : Type (u+1) :=
  ExactStructure.SmallK.{u+1} (supportedCoherentExactStructure j) n

end Quillen.CoherentScheme
