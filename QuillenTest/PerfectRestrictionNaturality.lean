/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ComparisonNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.GilletWaldhausen
public import Quillen.AlgebraicGeometry.Scheme.RestrictionFunctoriality
public import Quillen.AlgebraicGeometry.Scheme.Comparison.KToG

/-!
# Consumers of actual scheme/perfect restriction and comparison naturality

These check the original restriction maps, degree-zero comparisons, composed
open restrictions, and the inverse of the actual strict-perfect equivalence.
Coherent G-theory retains its locally noetherian hypotheses.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
universe u

example (X : Scheme.{u}) (n : ℕ) (x : StrictK X n) :
    strictKRestrict (𝟙 X) n x = x := by rw [strictKRestrict_id]; rfl

example (X : Scheme.{u}) (x : PerfectK X 0) :
    perfectKRestrict (𝟙 X) 0 x = x := by rw [perfectKRestrict_id]; rfl

example {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) (x : StrictK X n) :
    strictKRestrict (i ≫ j) n x = strictKRestrict i n (strictKRestrict j n x) := by
  rw [strictKRestrict_comp]
  rfl

example {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (x : PerfectK X 0) :
    perfectKRestrict (i ≫ j) 0 x = perfectKRestrict i 0 (perfectKRestrict j 0 x) := by
  rw [perfectKRestrict_comp]
  rfl

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) (x : StrictK X n) :
    perfectKRestrict j n (strictToPerfectKMap X n x) =
      strictToPerfectKMap U n (strictKRestrict j n x) :=
  DFunLike.congr_fun (strictToPerfectKMap_restrict j n) x

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (x : AlgebraicGeometry.Scheme.K X 0) :
    strictKRestrict j 0 (vectorBundleToStrictKMap X 0 x) =
      vectorBundleToStrictKMap U 0 (AlgebraicGeometry.Scheme.restrictK j 0 x) :=
  DFunLike.congr_fun (vectorBundleToStrictKMap_restrict j 0) x

example {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (x : AlgebraicGeometry.Scheme.K X 0) :
    perfectKRestrict (i ≫ j) 0 (vectorBundleToPerfectKMap X 0 x) =
      vectorBundleToPerfectKMap V 0
        (AlgebraicGeometry.Scheme.restrictK i 0 (AlgebraicGeometry.Scheme.restrictK j 0 x)) := by
  have h := DFunLike.congr_fun (vectorBundleToPerfectKMap_restrict (i ≫ j) 0) x
  simpa only [AlgebraicGeometry.Scheme.restrictK_comp, MonoidHom.comp_apply] using h

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (x : AlgebraicGeometry.Scheme.K X 0) :
    perfectKRestrict j 0
      (strictToPerfectKMap X 0 (vectorBundleToStrictKMap X 0 x)) =
      vectorBundleToPerfectKMap U 0 (AlgebraicGeometry.Scheme.restrictK j 0 x) := by
  change perfectKRestrict j 0 (vectorBundleToPerfectKMap X 0 x) = _
  exact DFunLike.congr_fun (vectorBundleToPerfectKMap_restrict j 0) x

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) (y : StrictK X n) :
    (vectorBundleToStrictKEquiv U n).symm (strictKRestrict j n y) =
      AlgebraicGeometry.Scheme.restrictK j n ((vectorBundleToStrictKEquiv X n).symm y) := by
  apply (vectorBundleToStrictKEquiv U n).injective
  rw [MulEquiv.apply_symm_apply]
  change strictKRestrict j n y = vectorBundleToStrictKMap U n
    (AlgebraicGeometry.Scheme.restrictK j n ((vectorBundleToStrictKEquiv X n).symm y))
  have h := DFunLike.congr_fun (vectorBundleToStrictKMap_restrict j n)
    ((vectorBundleToStrictKEquiv X n).symm y)
  change strictKRestrict j n ((vectorBundleToStrictKEquiv X n)
    ((vectorBundleToStrictKEquiv X n).symm y)) = _ at h
  simpa only [MulEquiv.apply_symm_apply, MonoidHom.comp_apply] using h

example {V U X : Scheme.{u}} [IsLocallyNoetherian V]
    [IsLocallyNoetherian U] [IsLocallyNoetherian X]
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (x : AlgebraicGeometry.Scheme.K X 0) :
    AlgebraicGeometry.Scheme.restrictG i 0
      (AlgebraicGeometry.Scheme.restrictG j 0 (AlgebraicGeometry.Scheme.KToG X 0 x)) =
      AlgebraicGeometry.Scheme.KToG V 0 (AlgebraicGeometry.Scheme.restrictK (i ≫ j) 0 x) := by
  change ((AlgebraicGeometry.Scheme.restrictG i 0).comp (AlgebraicGeometry.Scheme.restrictG j 0))
    (AlgebraicGeometry.Scheme.KToG X 0 x) = _
  rw [← AlgebraicGeometry.Scheme.restrictG_comp]
  exact AlgebraicGeometry.Scheme.KToG_restrict_apply (i ≫ j) 0 x
