/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineCechHigher
public import QuillenTest.AffineCechSections

/-!
# Actual higher Cech consumers over zero divisors and the empty affine scheme

The cover `[2, 3, 0]` of `Spec (ZMod 6)` exercises the original Cech complex in
degree one and every higher degree, including vanishing of actual homology.
The empty cover of `Spec (ZMod 1)` tests the empty index/ring edge case.
Geometric localization at the zero coordinate tests the empty principal chart.
-/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PrimeSpectrum Quillen.SchemeSheaf.AffineCech
open QuillenTest.AffineCechSections

namespace QuillenTest.AffineCechHigher

open Quillen

lemma torsion_cover_original_cech_exact
    (M : (Spec torsionRing).Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((cechComplexFunctor (fun i =>
      (basicOpen (coverCoordinates i) : (Spec torsionRing).Opens))).obj
        (modulesSpecToSheaf.obj M).obj).ExactAt (n + 1) :=
  principalCech_exactAt_succ M coverCoordinates coverCoordinates_cover n

lemma torsion_cover_original_cech_degree_one
    (M : (Spec torsionRing).Modules) [M.IsQuasicoherent] :
    ((cechComplexFunctor (fun i =>
      (basicOpen (coverCoordinates i) : (Spec torsionRing).Opens))).obj
        (modulesSpecToSheaf.obj M).obj).ExactAt 1 :=
  torsion_cover_original_cech_exact M 0

lemma torsion_cover_original_homology_zero
    (M : (Spec torsionRing).Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((cechComplexFunctor (fun i =>
      (basicOpen (coverCoordinates i) : (Spec torsionRing).Opens))).obj
        (modulesSpecToSheaf.obj M).obj).homology (n + 1)) :=
  (torsion_cover_original_cech_exact M n).isZero_homology

abbrev zeroRing : CommRingCat := CommRingCat.of (ZMod 1)

lemma empty_cover_exact (M : (Spec zeroRing).Modules) [M.IsQuasicoherent] (n : ℕ) :
    (principalCechComplex M (Fin.elim0 : Fin 0 → zeroRing)).ExactAt (n + 1) := by
  apply principalCech_exactAt_succ
  apply top_unique
  intro x _
  exact isEmptyElim x

lemma zero_coordinate_localized_cover_exact
    (M : (Spec (CommRingCat.of (Localization.Away (0 : torsionRing)))).Modules) (n : ℕ) :
    (principalCechComplex M (fun i =>
      algebraMap torsionRing (Localization.Away (0 : torsionRing)) (coverCoordinates i))).ExactAt
        (n + 1) := by
  let : IsLocalization.Away (coverCoordinates 2) (Localization.Away (0 : torsionRing)) := by
    change IsLocalization.Away (0 : torsionRing) (Localization.Away (0 : torsionRing))
    infer_instance
  exact principalCech_exactAt_succ_away coverCoordinates 2 _ M n

end QuillenTest.AffineCechHigher
