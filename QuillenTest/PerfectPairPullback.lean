/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairPullback

/-! # Consumers of actual arbitrary open-pair K-pullback

The square is neither assumed flat nor cartesian. Only the ambient schemes
are qc for maps on the original models; opens may be non-qc.
-/
@[expose] public section

open Quillen.PerfectComplexes


noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace QuillenTest.PerfectPairPullback

open Quillen

/-- The supported model map is still the actual geometric chain map. -/
theorem original_chain_map {A B : AlgebraicGeometry.Scheme.OpenPairs.{u}} (f : A ⟶ B)
    {K L : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory} (s : K ⟶ L) :
    ((boundedFlatPerfectSupportedPullback f).map s).hom =
      (AlgebraicGeometry.Scheme.Modules.Complex.pullback f.hom.right).map s.hom := rfl

/-- Relative weakness is preserved without any flatness or cartesian assumption. -/
theorem original_relative_weak {A B : AlgebraicGeometry.Scheme.OpenPairs.{u}} (f : A ⟶ B)
    {K L : BoundedFlatPerfect B.obj.right} (s : K ⟶ L)
    (hs : (boundedFlatPerfectOpenWaldhausen B.obj.hom).weq s) :
    (boundedFlatPerfectOpenWaldhausen A.obj.hom).weq
      ((boundedFlatPerfectPullback f.hom.right).map s) :=
  (boundedFlatPerfectOpenPullback_exact f).weak s hs

/-- Every original supported class is pulled back by actual representatives. -/
theorem original_supported_representative {A B : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (n : ℕ) (x : BoundedFlatPerfectSupportedK B.obj.obj.hom n) :
    perfectSupportedKPullback f n (boundedFlatPerfectSupportedToPerfectSupportedKMap B.obj.obj.hom n
      x) =
      boundedFlatPerfectSupportedToPerfectSupportedKMap A.obj.obj.hom n
        (boundedFlatPerfectSupportedKPullback f.hom n x) :=
  DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat f n) x

/-- Original supported pullback composes through three actual pair squares. -/
theorem supported_triple {A B C D : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (n : ℕ) :
    perfectSupportedKPullback (f ≫ g ≫ h) n =
      (perfectSupportedKPullback f n).comp
        ((perfectSupportedKPullback g n).comp (perfectSupportedKPullback h n)) := by
  rw [perfectSupportedKPullback_comp, perfectSupportedKPullback_comp]

/-- Original relative-open pullback composes, including degree zero. -/
theorem open_triple {A B C D : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    perfectOpenKPullback (f ≫ g ≫ h) 0 =
      (perfectOpenKPullback f 0).comp
        ((perfectOpenKPullback g 0).comp (perfectOpenKPullback h 0)) := by
  rw [perfectOpenKPullback_comp, perfectOpenKPullback_comp]

/-- The original supported inclusion commutes on the actual zero-degree classes. -/
theorem original_supported_zero_square {A B : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (x : PerfectSupportedK B.obj.obj.hom 0) :
    perfectKPullback f.hom.hom.right 0 (perfectSupportedKMap B.obj.obj.hom 0 x) =
      perfectSupportedKMap A.obj.obj.hom 0 (perfectSupportedKPullback f 0 x) :=
  DFunLike.congr_fun (perfectSupportedKMap_pullback f 0) x

/-- The unchanged original coarse map commutes on actual K-zero classes. -/
theorem original_coarse_zero_square {A B : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (x : PerfectK B.obj.obj.right 0) :
    perfectOpenKPullback f 0 (perfectOpenKMap B.obj.obj.hom 0 x) =
      perfectOpenKMap A.obj.obj.hom 0 (perfectKPullback f.hom.hom.right 0 x) :=
  DFunLike.congr_fun (perfectOpenKMap_pullback f 0) x

/-- The natural model isomorphism has exactly the original relative inclusion forward. -/
theorem original_comparison_forward (A : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ) (n :
  ℕ) :
    ((boundedFlatPerfectOpenNatIso n).hom.app A).hom =
      boundedFlatPerfectOpenToPerfectOpenKMap A.unop.obj.obj.hom n := rfl

/-- The original relative K-map is uniquely determined by its actual representative action. -/
theorem relative_map_unique {A B : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (n : ℕ) (k : PerfectOpenK B.obj.obj.hom n →* PerfectOpenK A.obj.obj.hom n)
    (h : ∀ x, k (boundedFlatPerfectOpenToPerfectOpenKMap B.obj.obj.hom n x) =
      boundedFlatPerfectOpenToPerfectOpenKMap A.obj.obj.hom n
        (boundedFlatPerfectOpenKPullback f.hom n x)) :
    k = perfectOpenKPullback f n :=
  perfectOpenKPullback_unique f n k (MonoidHom.ext h)

end QuillenTest.PerfectPairPullback
