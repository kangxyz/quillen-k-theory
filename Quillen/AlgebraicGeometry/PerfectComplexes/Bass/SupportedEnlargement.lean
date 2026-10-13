/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedForget
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.AuxiliaryNaturality

/-!
Actual support-enlargement maps in every negative Bass degree, with identity and composition laws
and preservation of the absolute class. Degree zero is proved equal to the old exact inclusion of
supported complexes. Neither acyclicity open is required qc.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.Bass
open Quillen.Scheme

/-- The genuine map enlarging support from X\V to X\U, induced by U ⊆ V. -/
def supportedNegativeKEnlarge (X : QuasiCompactSchemes.{u}) {U V : X.obj.Opens}
    (h : U ≤ V) (n : ℕ) :
    supportedNegativeK (Scheme.Bass.openSupportPair X V) n ⟶
      supportedNegativeK (Scheme.Bass.openSupportPair X U) n :=
  supportedNegativeKPullback (Scheme.Bass.openSupportPairMap X h) n

@[simp] lemma supportedNegativeKEnlarge_id (X : QuasiCompactSchemes.{u}) (U : X.obj.Opens) (n : ℕ) :
    supportedNegativeKEnlarge X (le_refl U) n = 𝟙 _ := by
  simp [supportedNegativeKEnlarge]

@[simp] lemma supportedNegativeKEnlarge_comp (X : QuasiCompactSchemes.{u}) {U V W : X.obj.Opens}
    (h : U ≤ V) (k : V ≤ W) (n : ℕ) :
    supportedNegativeKEnlarge X k n ≫ supportedNegativeKEnlarge X h n =
      supportedNegativeKEnlarge X (h.trans k) n := by
  simp only [supportedNegativeKEnlarge,←
    supportedNegativeKPullback_comp,Scheme.Bass.openSupportPairMap_comp]

/-- Degree zero is exactly the original pair-pullback support-enlargement map. -/
@[simp] lemma supportedNegativeKEnlarge_zero (X : QuasiCompactSchemes.{u}) {U V : X.obj.Opens}
    (h : U ≤ V) (a : PerfectSupportedK V.ι 0) :
    supportedNegativeKEnlarge X h 0 (Additive.ofMul a) =
      Additive.ofMul (perfectSupportedKPullback (Scheme.Bass.openSupportPairMap X h) 0 a) := rfl

/-- Enlarging support preserves the literal absolute Bass class in every degree. -/
@[reassoc] lemma supportedNegativeKEnlarge_forget (X : QuasiCompactSchemes.{u}) {U V : X.obj.Opens}
    (h : U ≤ V) (n : ℕ) :
    supportedNegativeKEnlarge X h n ≫ supportedNegativeKForget (Scheme.Bass.openSupportPair X U) n =
      supportedNegativeKForget (Scheme.Bass.openSupportPair X V) n := by
  have hnat := supportedNegativeKForget_naturality (Scheme.Bass.openSupportPairMap X h) n
  rw [Scheme.Bass.openSupportPairMap_base] at hnat
  change supportedNegativeKEnlarge X h n ≫ supportedNegativeKForget (Scheme.Bass.openSupportPair X
    U) n =
    supportedNegativeKForget (Scheme.Bass.openSupportPair X V) n ≫ negativeKPullback (𝟙 X) n at hnat
  rw [negativeKPullback_id] at hnat
  exact hnat.trans (Category.comp_id _)

/-- The seed enlargement is literally the original exact inclusion of supported complexes. -/
lemma supportedNegativeKEnlarge_zero_original (X : QuasiCompactSchemes.{u}) {U V : X.obj.Opens}
    (h : U ≤ V) (a : PerfectSupportedK V.ι 0) :
    supportedNegativeKEnlarge X h 0 (Additive.ofMul a) =
      Additive.ofMul (perfectSupportedChangeOpenKMap h 0 a) := by
  rw [supportedNegativeKEnlarge_zero,perfectSupportedChangeOpenKMap_eq_pullback]
  rfl

end Quillen.PerfectComplexes.Bass

end
