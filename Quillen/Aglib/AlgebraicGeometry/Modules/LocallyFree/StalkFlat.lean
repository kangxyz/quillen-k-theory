/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.AlgebraicGeometry.Modules.Flat.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalSplitting
public import Aglib.AlgebraicGeometry.Modules.Flat.Locality
public import Quillen.Aglib.AlgebraicGeometry.Modules.Flat.Retracts
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.Flat.Closure

/-!
# Actual module stalks of vector bundles are flat

The genuine flat-cover epimorphism locally splits onto a finite locally free
quotient. Local retract closure and the original open-stalk comparison then
prove stalkwise flatness. Global projectivity and global splitting are not
assumed, and no affine or quasicoherent replacement is substituted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- A vector bundle is a local retract of the genuine flat cover; stalk flatness
therefore follows from actual local splitting, without assuming global projectivity. -/
theorem stalkwiseFlat_of_finiteLocallyFree {X : Scheme.{u}} (M : X.Modules)
    [IsFiniteLocallyFree X M] : stalkwiseFlat X M := by
  intro x
  obtain ⟨U, hxU, G, hG, hfin⟩ :=
    finiteLocallyFree_iff_pointwise.mp (inferInstance : IsFiniteLocallyFree X M) x
  obtain ⟨V, _, hxV, s, hs⟩ :=
    exists_local_section_of_finite_basis (flatCoverπ M) U G x hxU
  let e := Scheme.Modules.overFunctorEquiv V
  let sV : M.restrict V.ι ⟶ (flatCover M).restrict V.ι :=
    (e.app M).inv ≫ (Scheme.Modules.overEquiv V).functor.map s ≫ (e.app (flatCover M)).hom
  have hsV : sV ≫ (Scheme.Modules.restrictFunctor V.ι).map (flatCoverπ M) = 𝟙 _ := by
    dsimp only [sV]
    have hn := e.hom.naturality (flatCoverπ M)
    dsimp only [Functor.comp_map] at hn
    simp only [Category.assoc]
    erw [← hn, ← Functor.map_comp_assoc, hs]
    simp
  have hflat : stalkwiseFlat V.toScheme ((flatCover M).restrict V.ι) := by
    apply (stalkwiseFlat V.toScheme).prop_of_iso
      (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app (flatCover M)).symm)
    exact stalkwiseFlat_pullback V.ι (flatCover_stalkwiseFlat M)
  have hM := stalkwiseFlat_of_retract ⟨sV,
    (Scheme.Modules.restrictFunctor V.ι).map (flatCoverπ M), hsV⟩ hflat
  exact stalk_flat_of_restrict V.ι ⟨x, hxV⟩ M (hM ⟨x, hxV⟩)

end AlgebraicGeometry.Scheme.Modules
