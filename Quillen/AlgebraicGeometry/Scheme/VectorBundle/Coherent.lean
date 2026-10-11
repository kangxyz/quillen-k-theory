/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Comparison.AffineFinite
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction

/-! # Exact inclusion of vector bundles into coherent sheaves

Finite local bases imply affine-local finite quasicoherence. Over locally
noetherian schemes, the original inclusion preserves and reflects the
inherited short exact sequences and commutes with original open restriction.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf

/-- A finite locally free sheaf is affine-locally quasicoherent of finite type.
No noetherianity is needed for this assertion about the object property. -/
theorem coherent_of_finiteLocallyFree {X : Scheme.{u}} (M : X.Modules)
    [IsFiniteLocallyFree X M] : CoherentScheme.affineLocallyFiniteType X M := by
  intro R j _
  exact affineFiniteSheaf_of_finiteLocallyFree R
    ((Scheme.Modules.restrictFunctor j).obj M)

/-- The actual finite-local-freeness property implies the coherent object
property on every scheme. -/
theorem finiteLocallyFree_le_coherent {X : Scheme.{u}} :
    finiteLocallyFree X ≤ CoherentScheme.affineLocallyFiniteType X := by
  intro M hM
  exact coherent_of_finiteLocallyFree M

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The fully faithful inclusion of actual vector bundles into coherent sheaves. -/
def vectorBundleToCoherent : FiniteLocallyFree X ⥤ CoherentScheme.FiniteTypeSheaves X :=
  ObjectProperty.ιOfLE (finiteLocallyFree_le_coherent (X := X))

instance vectorBundleToCoherent_full : (vectorBundleToCoherent X).Full := by
  dsimp [vectorBundleToCoherent]
  infer_instance

instance vectorBundleToCoherent_faithful : (vectorBundleToCoherent X).Faithful := by
  dsimp [vectorBundleToCoherent]
  infer_instance

instance vectorBundleToCoherent_additive : (vectorBundleToCoherent X).Additive where
  map_add := by intros; rfl

omit [IsLocallyNoetherian X] in
/-- The inclusion preserves the underlying module sheaf and all morphisms. -/
@[simp]
theorem vectorBundleToCoherent_comp_inclusion :
    vectorBundleToCoherent X ⋙ CoherentScheme.finiteTypeSheavesToModules X =
      (finiteLocallyFree X).ι := rfl

/-- A vector-bundle conflation is exactly a short exact sequence of its coherent
sheaves; neither side requires a global splitting. -/
theorem vectorBundleToCoherent_shortExact_iff (S : ShortComplex (FiniteLocallyFree X)) :
    (vectorBundleExactStructure X).conflation S ↔
      (S.map (vectorBundleToCoherent X)).ShortExact := by
  rw [CoherentScheme.coherent_shortExact_iff]
  rfl

/-- The genuine vector-bundle inclusion is exact for the inherited vector-bundle
structure and the abelian coherent-sheaf structure. -/
def vectorBundleToCoherentExact :
    ExactFunctor (vectorBundleExactStructure X) (CoherentScheme.coherentExactStructure X) where
  toFunctor := vectorBundleToCoherent X
  map_conflation S hS := (vectorBundleToCoherent_shortExact_iff X S).mp hS

variable {X} {U : Scheme.{u}} [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

omit [IsLocallyNoetherian X] [IsLocallyNoetherian U] in
/-- Restricting a vector bundle and then including it among finite-type quasicoherent
sheaves agrees with first including and then geometrically restricting it. -/
theorem vectorBundleToCoherent_restrict :
    vectorBundleToCoherent X ⋙ CoherentScheme.finiteTypeSheavesRestriction j =
      vectorBundleRestrict j ⋙ vectorBundleToCoherent U := rfl

/-- The exact-functor comparison uses the identical underlying geometric
restriction on both sides. -/
def vectorBundleToCoherentRestrictIso :
    ((vectorBundleToCoherentExact X).comp
      (CoherentScheme.coherentRestrictionExact j)).toFunctor ≅
    ((vectorBundleExactRestrict j).comp
      (vectorBundleToCoherentExact U)).toFunctor := Iso.refl _

end Quillen.SchemeSheaf
