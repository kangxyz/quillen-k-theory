/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ConnectingNaturality

/-! # Semantic consumers of the original open-pair connecting square -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.Waldhausen Quillen.Waldhausen.Fibration
universe u
namespace QuillenTest.PerfectConnectingNaturality

/-- Both exact flattening directions retain every actual complex map. -/
theorem actual_supported_map_roundtrip {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K L : (boundedFlatPerfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (boundedFlatPerfectAcyclicToSupported j).map
      ((boundedFlatPerfectSupportedToAcyclic j).map f) = f := rfl

/-- The original canonical bounded-flat fiber comparison has full strict HELP. -/
theorem boundedFlat_original_fiber_has_HELP {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Quillen.FiniteCubeStrictHELP (canonicalFiberMap (boundedFlatPerfectOpenNested j)) :=
  (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j).cube_strictHELP

/-- The boundary comparison at K₁→K₀ uses the original inclusion on both sides. -/
theorem original_boundary_zero_comparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (x : BoundedFlatPerfectOpenK j 1) :
    boundedFlatPerfectSupportedToPerfectSupportedKMap j 0 (boundedFlatPerfectOpenConnectingHom j 0
      x) =
      perfectOpenConnectingHom j 0 (boundedFlatPerfectOpenToPerfectOpenKMap j 1 x) :=
  DFunLike.congr_fun (boundedFlatPerfectOpenConnectingHom_comparison j 0) x

variable {A B C : Quillen.Scheme.QuasiCompactOpenPairs.{u}}

/-- Arbitrary pair pullback commutes with the original K₁-to-supported-K₀ boundary. -/
theorem original_boundary_zero_pullback (f : A ⟶ B) (x : PerfectOpenK B.obj.obj.hom 1) :
    perfectSupportedKPullback f 0 (perfectOpenConnectingHom B.obj.obj.hom 0 x) =
      perfectOpenConnectingHom A.obj.obj.hom 0 (perfectOpenKPullback f 1 x) :=
  DFunLike.congr_fun (perfectOpenConnectingHom_pullback f 0) x

/-- An original boundary-zero class remains boundary-zero after geometric pullback. -/
theorem original_boundary_kernel_preserved (f : A ⟶ B) (n : ℕ)
    (x : PerfectOpenK B.obj.obj.hom (n+1)) (hx : perfectOpenConnectingHom B.obj.obj.hom n x = 1) :
    perfectOpenConnectingHom A.obj.obj.hom n (perfectOpenKPullback f (n+1) x) = 1 := by
  have h := DFunLike.congr_fun (perfectOpenConnectingHom_pullback f n) x
  simp only [MonoidHom.comp_apply] at h
  rw [← h, hx, map_one]

/-- A prescribed boundary class pulls back to the boundary of its prescribed original lift. -/
theorem original_boundary_lift_preserved (f : A ⟶ B) (n : ℕ)
    (x : PerfectOpenK B.obj.obj.hom (n+1)) (y : PerfectSupportedK B.obj.obj.hom n)
    (hxy : perfectOpenConnectingHom B.obj.obj.hom n x = y) :
    perfectOpenConnectingHom A.obj.obj.hom n (perfectOpenKPullback f (n+1) x) =
      perfectSupportedKPullback f n y := by
  have h := DFunLike.congr_fun (perfectOpenConnectingHom_pullback f n) x
  simp only [MonoidHom.comp_apply] at h
  rw [← h, hxy]

/-- Two successive pair pullbacks retain the original boundary square. -/
theorem original_boundary_composite_pullback (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    ((perfectSupportedKPullback f n).comp (perfectSupportedKPullback g n)).comp
      (perfectOpenConnectingHom C.obj.obj.hom n) =
    (perfectOpenConnectingHom A.obj.obj.hom n).comp
      ((perfectOpenKPullback f (n+1)).comp (perfectOpenKPullback g (n+1))) := by
  rw [← perfectSupportedKPullback_comp, ← perfectOpenKPullback_comp]
  exact perfectOpenConnectingHom_pullback (f ≫ g) n

end QuillenTest.PerfectConnectingNaturality
