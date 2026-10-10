/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.BoundedFlat.KComparison

/-!
# Arbitrary pullback on original perfect K-groups of quasi-compact schemes

The literal bounded-flat inclusion is already proved to induce a K-equivalence.
Transporting actual geometric bounded-flat pullback through that equivalence
therefore defines maps on the original locally-perfect K-groups. Their actual
representative square uniquely specifies them. Identity/composition and the
original strict/vector-bundle comparison naturality hold in every connective
degree. Flat maps and open immersions retain their earlier original maps.
Quasi-compactness is explicit on both schemes; no global uniform bound on
arbitrary non-quasi-compact perfect complexes is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes

/-- Derived pullback on the original perfect K-groups, transported through the
proved bounded-flat model by its literal inclusion comparison. -/
def perfectKPullback {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (n : ℕ) : PerfectK Y n →* PerfectK X n :=
  (boundedFlatPerfectKEquiv X n).toMonoidHom.comp
    ((boundedFlatPerfectKPullback f n).comp (boundedFlatPerfectKEquiv Y n).symm.toMonoidHom)

/-- The new map is computed by actual geometric pullback on bounded-flat representatives. -/
theorem perfectKPullback_comp_boundedFlat {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) (n : ℕ) :
    (perfectKPullback f n).comp (boundedFlatPerfectToPerfectKMap Y n) =
      (boundedFlatPerfectToPerfectKMap X n).comp (boundedFlatPerfectKPullback f n) := by
  ext x
  change boundedFlatPerfectKEquiv X n
    (boundedFlatPerfectKPullback f n ((boundedFlatPerfectKEquiv Y n).symm
      (boundedFlatPerfectKEquiv Y n x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The representative square uniquely specifies the original perfect K-map. -/
theorem perfectKPullback_unique {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (n : ℕ) (k : PerfectK Y n →* PerfectK X n)
    (hk : k.comp (boundedFlatPerfectToPerfectKMap Y n) =
      (boundedFlatPerfectToPerfectKMap X n).comp (boundedFlatPerfectKPullback f n)) :
    k = perfectKPullback f n := by
  ext x
  obtain ⟨y, rfl⟩ := (boundedFlatPerfectToPerfectKMap_bijective Y n).surjective x
  exact DFunLike.congr_fun (hk.trans (perfectKPullback_comp_boundedFlat f n).symm) y

@[simp] theorem perfectKPullback_id (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    perfectKPullback (𝟙 X) n = MonoidHom.id (PerfectK X n) := by
  symm
  apply perfectKPullback_unique
  simp only [boundedFlatPerfectKPullback_id, MonoidHom.id_comp, MonoidHom.comp_id]

@[simp] theorem perfectKPullback_comp {X Y Z : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] [CompactSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    perfectKPullback (f ≫ g) n = (perfectKPullback f n).comp (perfectKPullback g n) := by
  symm
  apply perfectKPullback_unique
  rw [MonoidHom.comp_assoc, perfectKPullback_comp_boundedFlat,
    ← MonoidHom.comp_assoc, perfectKPullback_comp_boundedFlat,
    MonoidHom.comp_assoc, boundedFlatPerfectKPullback_comp]

/-- On flat maps this agrees with the previously constructed original exact pullback. -/
theorem perfectKPullback_eq_flatPullback {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) [Flat f] (n : ℕ) :
    perfectKPullback f n = perfectKFlatPullback f n :=
  (perfectKPullback_unique f n (perfectKFlatPullback f n)
    (boundedFlatPerfectToPerfectKMap_flatPullback f n)).symm

/-- Open restriction retains the original public perfect K-map. -/
theorem perfectKPullback_eq_restrict {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    perfectKPullback j n = perfectKRestrict j n :=
  (perfectKPullback_eq_flatPullback j n).trans (perfectKFlatPullback_eq_restrict j n)

/-- The original strict-to-local comparison is natural for arbitrary maps of qc schemes. -/
theorem strictToPerfectKMap_pullback {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) (n : ℕ) :
    (perfectKPullback f n).comp (strictToPerfectKMap Y n) =
      (strictToPerfectKMap X n).comp (strictKPullback f n) := by
  rw [← boundedFlatPerfectToPerfect_comp_strict Y,
    ← MonoidHom.comp_assoc, perfectKPullback_comp_boundedFlat,
    MonoidHom.comp_assoc, strictToBoundedFlatPerfectKMap_pullback,
    ← MonoidHom.comp_assoc, boundedFlatPerfectToPerfect_comp_strict]

/-- The original public vector-bundle comparison is natural for arbitrary qc scheme maps. -/
theorem vectorBundleToPerfectKMap_pullback {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) (n : ℕ) :
    (perfectKPullback f n).comp (vectorBundleToPerfectKMap Y n) =
      (vectorBundleToPerfectKMap X n).comp (Quillen.Scheme.pullbackK f n) := by
  rw [← strictToPerfect_comp_vectorBundleToStrictKMap Y,
    ← MonoidHom.comp_assoc, strictToPerfectKMap_pullback,
    MonoidHom.comp_assoc, vectorBundleToStrictKMap_pullback,
    ← MonoidHom.comp_assoc, strictToPerfect_comp_vectorBundleToStrictKMap]

end Quillen.PerfectComplexes
