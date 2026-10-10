/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.ConcentratedHomology
public import Quillen.AlgebraicGeometry.PerfectComplexes.Homology
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Locality

/-! # Actual concentrated vector-bundle homology from open-cover models -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u v
namespace Quillen.PerfectComplexes
variable {X : Scheme.{u}} (K : Complex X) {ι : Type v}
  (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
  (hj : ∀ x : X, ∃ i, ∃ y : Y i, j i y = x)
include hj

/-- Exactness of the original complex is detected by arbitrary covering open immersions. -/
theorem exactAt_of_openImmersionCover (n : ℤ)
    (hK : ∀ i, ((restrict (j i)).obj K).ExactAt n) : K.ExactAt n := by
  rw [exactAt_iff_isZero_homology]
  apply (SchemeSheaf.isZero_iff_stalks (K.homology n)).mpr
  intro x
  obtain ⟨i, y, rfl⟩ := hj x
  have hz : IsZero ((Scheme.Modules.restrictFunctor (j i)).obj (K.homology n)) :=
    ((exactAt_iff_isZero_homology _ _).mp (hK i)).of_iso (restrictHomologyIso (j i) K n).symm
  exact ((SchemeSheaf.stalkFunctor (Y i) y).map_isZero hz).of_iso
    ((Scheme.Modules.restrictStalkNatIso (j i) y).app (K.homology n)).symm

/-- Original upper cohomological bounds descend from covering open immersions. -/
theorem isLE_of_openImmersionCover (n : ℤ)
    (hK : ∀ i, ((restrict (j i)).obj K).IsLE n) : K.IsLE n := by
  rw [CochainComplex.isLE_iff]
  intro k hk
  exact exactAt_of_openImmersionCover K Y j hj k (fun i =>
    let := hK i
    ((restrict (j i)).obj K).exactAt_of_isLE n k hk)

/-- Original lower cohomological bounds descend from covering open immersions. -/
theorem isGE_of_openImmersionCover (n : ℤ)
    (hK : ∀ i, ((restrict (j i)).obj K).IsGE n) : K.IsGE n := by
  rw [CochainComplex.isGE_iff]
  intro k hk
  exact exactAt_of_openImmersionCover K Y j hj k (fun i =>
    let := hK i
    ((restrict (j i)).obj K).exactAt_of_isGE n k hk)

/-- Finite local freeness of the original homology sheaf descends from the actual
homology sheaves of the restricted complexes. -/
theorem finiteLocallyFree_homology_of_openImmersionCover (n : ℤ)
    (hK : ∀ i, SchemeSheaf.IsFiniteLocallyFree (Y i) (((restrict (j i)).obj K).homology n)) :
    SchemeSheaf.IsFiniteLocallyFree X (K.homology n) := by
  apply SchemeSheaf.finiteLocallyFree_of_openImmersionCover (K.homology n) Y j hj
  intro i
  let := hK i
  exact SchemeSheaf.finiteLocallyFree_of_iso (restrictHomologyIso (j i) K n)

/-- Coverwise concentrated vector-bundle homology gives the genuine original
derived single model on the original homology sheaf. -/
theorem exists_vectorBundle_single_of_openImmersionCover (n : ℤ)
    (hlo : ∀ i, ((restrict (j i)).obj K).IsGE n)
    (hhi : ∀ i, ((restrict (j i)).obj K).IsLE n)
    (hvb : ∀ i, SchemeSheaf.IsFiniteLocallyFree (Y i) (((restrict (j i)).obj K).homology n)) :
    SchemeSheaf.IsFiniteLocallyFree X (K.homology n) ∧
      Nonempty ((toDerived X).obj K ≅ (toDerived X).obj
        ((CochainComplex.singleFunctor X.Modules n).obj (K.homology n))) := by
  have := isGE_of_openImmersionCover K Y j hj n hlo
  have := isLE_of_openImmersionCover K Y j hj n hhi
  let : HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
  exact ⟨finiteLocallyFree_homology_of_openImmersionCover K Y j hj n hvb,
    ⟨Quillen.CochainComplex.derivedSingleHomologyIso K n⟩⟩

end Quillen.PerfectComplexes
