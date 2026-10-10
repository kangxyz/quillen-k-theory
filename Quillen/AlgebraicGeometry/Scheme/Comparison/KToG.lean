/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Comparison.AffineFinite
public import Quillen.AlgebraicGeometry.Scheme.KTheory
public import Quillen.AlgebraicGeometry.Scheme.GTheory
public import Quillen.CategoryTheory.SmallModel.Functoriality

/-!
# The canonical comparison from scheme K-theory to coherent G-theory

Finite locally free sheaves satisfy the affine-local finite quasicoherent
condition on every scheme. On a locally noetherian scheme their actual full
inclusion into coherent sheaves is exact for the ambient short exact
sequences. Its canonical small-model K-map is the comparison from K to G.
The comparison commutes with actual geometric open restriction.
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

/-- The canonical comparison is the small-model K-map of the actual exact inclusion. -/
def schemeKToG (n : ℕ) : SchemeK X n →* CoherentScheme.G X n :=
  (vectorBundleToCoherentExact X).smallKMap n

@[simp]
theorem schemeKToG_eq_smallKMap (n : ℕ) :
    schemeKToG X n = (vectorBundleToCoherentExact X).smallKMap n := rfl

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

/-- The canonical K-to-G comparison commutes with actual open restriction. -/
theorem schemeKToG_restrict (n : ℕ) :
    (CoherentScheme.restrictionGMap j n).comp (schemeKToG X n) =
      (schemeKToG U n).comp (schemeKRestrict j n) := by
  change ((CoherentScheme.coherentRestrictionExact j).smallKMap n).comp
      ((vectorBundleToCoherentExact X).smallKMap n) =
    ((vectorBundleToCoherentExact U).smallKMap n).comp
      ((vectorBundleExactRestrict j).smallKMap n)
  rw [← ExactFunctor.smallKMap_comp, ← ExactFunctor.smallKMap_comp]
  exact ExactFunctor.smallKMap_eq_of_natIso (vectorBundleToCoherentRestrictIso j) n

/-- Elementwise naturality of the comparison. -/
theorem schemeKToG_restrict_apply (n : ℕ) (x : SchemeK X n) :
    CoherentScheme.restrictionGMap j n (schemeKToG X n x) =
      schemeKToG U n (schemeKRestrict j n x) :=
  DFunLike.congr_fun (schemeKToG_restrict j n) x

end Quillen.SchemeSheaf

namespace Quillen.Scheme

/-- The canonical comparison from genuine scheme K-theory to coherent G-theory. -/
def KToG (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    K X n →* G X n := SchemeSheaf.schemeKToG X n

@[simp]
theorem KToG_eq_smallKMap (X : AlgebraicGeometry.Scheme.{u})
    [IsLocallyNoetherian X] (n : ℕ) :
    KToG X n = (SchemeSheaf.vectorBundleToCoherentExact X).smallKMap n := rfl

/-- The public comparison is natural for actual open restriction on K and G. -/
theorem KToG_restrict {U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (restrictG j n).comp (KToG X n) = (KToG U n).comp (restrictK j n) :=
  SchemeSheaf.schemeKToG_restrict j n

/-- The pointwise form of the public restriction square. -/
theorem KToG_restrict_apply {U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) (x : K X n) :
    restrictG j n (KToG X n x) = KToG U n (restrictK j n x) :=
  DFunLike.congr_fun (KToG_restrict j n) x

end Quillen.Scheme
