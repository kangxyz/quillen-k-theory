/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.PairRestriction

/-! # Consumers of the original perfect restriction endpoint square -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes
universe u
namespace Quillen.Tests.PerfectPairRestriction

/-- Relative weakness is exactly enough for restriction to actual bounded-flat complexes. -/
theorem relative_weak_restriction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K L : BoundedFlatPerfect X} (s : K ⟶ L)
    (hs : (boundedFlatPerfectOpenWaldhausen j).weq s) :
    (boundedFlatPerfectWaldhausen U).weq ((boundedFlatPerfectPullback j).map s) :=
  (boundedFlatPerfectOpenRestriction_exact j).weak s hs

/-- The actual model restriction square needs no quasi-compactness hypotheses. -/
theorem model_square {A B : Quillen.Scheme.OpenPairs.{u}} (f : A ⟶ B) (n : ℕ)
    (x : BoundedFlatPerfectOpenK B.obj.hom n) :
    boundedFlatPerfectKPullback f.hom.left n (boundedFlatPerfectOpenKRestrict B.obj.hom n x) =
      boundedFlatPerfectOpenKRestrict A.obj.hom n (boundedFlatPerfectOpenKPullback f n x) :=
  DFunLike.congr_fun (boundedFlatPerfectOpenKRestrict_pullback f n) x

/-- Original relative restriction commutes in every degree with exact qc hypotheses. -/
theorem original_endpoint_square {A B : Quillen.Scheme.QuasiCompactOpenPairs.{u}}
    [CompactSpace A.obj.obj.left] [CompactSpace B.obj.obj.left]
    (f : A ⟶ B) (n : ℕ) (x : PerfectOpenK B.obj.obj.hom n) :
    perfectKPullback f.hom.hom.left n (perfectOpenKRestrict B.obj.obj.hom n x) =
      perfectOpenKRestrict A.obj.obj.hom n (perfectOpenKPullback f n x) :=
  DFunLike.congr_fun (perfectOpenKRestrict_pullback f n) x

/-- The ordinary original perfect restriction square follows even in degree zero. -/
theorem original_zero_square {A B : Quillen.Scheme.QuasiCompactOpenPairs.{u}}
    [CompactSpace A.obj.obj.left] [CompactSpace B.obj.obj.left]
    (f : A ⟶ B) (x : PerfectK B.obj.obj.right 0) :
    perfectKPullback f.hom.hom.left 0 (perfectKRestrict B.obj.obj.hom 0 x) =
      perfectKRestrict A.obj.obj.hom 0 (perfectKPullback f.hom.hom.right 0 x) :=
  DFunLike.congr_fun (perfectKRestrict_pairPullback f 0) x

end Quillen.Tests.PerfectPairRestriction
