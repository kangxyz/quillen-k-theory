/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.OmegaSpectrum
public import Quillen.Waldhausen.Functoriality.KMap

/-! Actual spectrum maps of arbitrary original exact functors, retaining the public K-map.
Canonical zero normalization removes the chosen-zero-image equality hypothesis. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Waldhausen.IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Every original exact functor has an actual spectrum map, using the existing
canonical zero rebase rather than requiring equality of the original zero image. -/
def exactOriginalPrespectrumMap : originalPrespectrum W ⟶ originalPrespectrum V :=
  originalPrespectrumMap W V hF.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _)

/-- The same unchanged map between the proved actual Omega-spectra. -/
def exactOriginalOmegaSpectrumMap : originalOmegaSpectrum W ⟶ originalOmegaSpectrum V :=
  ObjectProperty.homMk (exactOriginalPrespectrumMap W V hF)

/-- The induced homotopy-set map retains the original public KMap. -/
lemma exactOriginalZeroSpaceEquiv_naturality (n : ℕ) (a : W.K n) :
    originalZeroSpaceEquiv V n (KMap hF n a) =
      homotopyGroupMap ((exactOriginalPrespectrumMap W V hF).map 0)
        ((exactOriginalPrespectrumMap W V hF).map_point 0) (originalZeroSpaceEquiv W n a) := by
  have h := KMap_eq_of_iso hF hF.rebase
    (Quillen.rebaseFunctorIso F W.zero V.zero ((hF.zero W.isZero).iso V.isZero)) n
  rw [h]
  exact originalZeroSpaceEquiv_naturality W V hF.rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _) n a

end Quillen.Waldhausen.IteratedS
