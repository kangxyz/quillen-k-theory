/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPullbackFunctor

/-! # Consumers of original perfect derived K-pullback

Arbitrary morphisms of quasi-compact schemes require no flatness hypothesis.
These tests use actual bounded-flat representatives, uniqueness, composition,
and the unchanged original comparison maps, including degree zero.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes
universe u
namespace Quillen.Tests.PerfectDerivedPullback

/-- Evaluation on an actual bounded-flat representative gives genuine geometric pullback. -/
theorem actual_representative {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (n : ℕ) (x : BoundedFlatPerfectK Y n) :
    perfectKPullback f n (boundedFlatPerfectToPerfectKMap Y n x) =
      boundedFlatPerfectToPerfectKMap X n (boundedFlatPerfectKPullback f n x) :=
  DFunLike.congr_fun (perfectKPullback_comp_boundedFlat f n) x

/-- The actual representative action determines the entire original degree-zero map. -/
theorem unique_zero_map {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (k : PerfectK Y 0 →* PerfectK X 0)
    (h : ∀ x, k (boundedFlatPerfectToPerfectKMap Y 0 x) =
      boundedFlatPerfectToPerfectKMap X 0 (boundedFlatPerfectKPullback f 0 x)) :
    k = perfectKPullback f 0 :=
  perfectKPullback_unique f 0 k (MonoidHom.ext h)

/-- Three genuinely arbitrary scheme morphisms compose on all original K-groups. -/
theorem triple_composition {W X Y Z : Scheme.{u}}
    [CompactSpace W] [CompactSpace X] [CompactSpace Y] [CompactSpace Z]
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ) :
    perfectKPullback (f ≫ g ≫ h) n =
      (perfectKPullback f n).comp ((perfectKPullback g n).comp (perfectKPullback h n)) := by
  rw [perfectKPullback_comp, perfectKPullback_comp]

/-- Flat comparison is with the earlier original exact functor's map. -/
theorem original_flat_map {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) [Flat f] (n : ℕ) :
    perfectKPullback f n = perfectKFlatPullback f n := perfectKPullback_eq_flatPullback f n

/-- Open restriction retains the old public map even in degree zero. -/
theorem original_open_map {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (j : X ⟶ Y) [IsOpenImmersion j] :
    perfectKPullback j 0 = perfectKRestrict j 0 := perfectKPullback_eq_restrict j 0

/-- The original vector-bundle comparison commutes with arbitrary pullback in degree zero. -/
theorem vector_bundle_zero {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (x : Quillen.Scheme.K Y 0) :
    perfectKPullback f 0 (vectorBundleToPerfectKMap Y 0 x) =
      vectorBundleToPerfectKMap X 0 (Quillen.Scheme.pullbackK f 0 x) :=
  DFunLike.congr_fun (vectorBundleToPerfectKMap_pullback f 0) x

/-- The inverse of the genuine model comparison is natural as well. -/
theorem original_inverse_comparison {X Y : Quillen.Scheme.QuasiCompactSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((boundedFlatPerfectToPerfectNatIso n).inv.app Y).hom.comp
        (perfectKPullback f.unop.hom n) =
      (boundedFlatPerfectKPullback f.unop.hom n).comp
        ((boundedFlatPerfectToPerfectNatIso n).inv.app X).hom :=
  GrpCat.hom_ext_iff.mp ((boundedFlatPerfectToPerfectNatIso n).inv.naturality f)

/-- The bundled original functor retains its literal new original-group map. -/
theorem bundled_map {X Y : Quillen.Scheme.QuasiCompactSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((PerfectKFunctor n).map f).hom = perfectKPullback f.unop.hom n := rfl

end Quillen.Tests.PerfectDerivedPullback
