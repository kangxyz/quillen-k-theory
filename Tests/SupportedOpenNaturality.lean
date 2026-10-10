/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.AuxiliaryNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedOpenComparison

/-!
# Naturality of supported open K-theory

Regression statements express support-change squares for the boundary,
degree-zero restriction, and positive-degree inverse lifts using public pair
maps. The bounded-flat statements record a unique degree-zero lift, the
change-of-weak-equivalences square, and a relative approximation factorization.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.Tests.SupportedOpenNaturality
open PerfectComplexes
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] {S T : X.Opens} (h : S ≤ T)
  (hS : IsCompact (S : Set X)) (hT : IsCompact (T : Set X))

/-- The boundary square is literally a square of the existing public pair maps. -/
theorem original_public_boundary_square (n : ℕ)
    (x : PerfectSupportedK (j ⁻¹ᵁ T).ι (n+1)) :
    perfectSupportedKPullback (qcSupportChangeOpenPair (sup_le_sup_right h j.opensRange)) n
        (qcqsPerfectSupportedConnectingHom j T hT n x) =
      qcqsPerfectSupportedConnectingHom j S hS n
        (perfectSupportedKPullback (qcSupportChangeOpenPair
          (show j ⁻¹ᵁ S ≤ j ⁻¹ᵁ T from fun _ hx => h hx)) (n+1) x) := by
  rw [← perfectSupportedChangeOpenKMap_eq_pullback (sup_le_sup_right h j.opensRange) n,
    ← perfectSupportedChangeOpenKMap_eq_pullback (show j ⁻¹ᵁ S ≤ j ⁻¹ᵁ T from fun _ hx => h hx)
      (n+1)]
  exact DFunLike.congr_fun (qcqsPerfectSupportedConnectingHom_changeOpen j h hS hT n) x

omit [QuasiSeparatedSpace X] in
/-- The original K0 source restriction square has no supplied lift or surjectivity. -/
theorem original_public_KZero_restriction_square (x : PerfectSupportedK T.ι 0) :
    perfectSupportedKPullback (qcSupportRestrictionPair j S) 0
        (perfectSupportedKPullback (qcSupportChangeOpenPair h) 0 x) =
      perfectSupportedKPullback (qcSupportChangeOpenPair
          (show j ⁻¹ᵁ S ≤ j ⁻¹ᵁ T from fun _ hx => h hx)) 0
        (perfectSupportedKPullback (qcSupportRestrictionPair j T) 0 x) := by
  rw [← perfectSupportedKRestrict_eq_pullback j S 0, ← perfectSupportedKRestrict_eq_pullback j T 0,
    ← perfectSupportedChangeOpenKMap_eq_pullback h 0,
    ← perfectSupportedChangeOpenKMap_eq_pullback (show j ⁻¹ᵁ S ≤ j ⁻¹ᵁ T from fun _ hx => h hx) 0]
  exact DFunLike.congr_fun (perfectSupportedChangeOpenKMap_comp_restrict j h 0) x

/-- The actual relative inverse lift is compatible with weakening support. -/
theorem original_inverse_square (n : ℕ)
    (x : PerfectSupportedK (j ⁻¹ᵁ T).ι (n+1)) :
    perfectSupportedOpenChangeOpenKMap j h (n+1)
        ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x) =
      (qcqsPerfectSupportedOpenKEquiv j S hS n).symm
        (perfectSupportedKPullback (qcSupportChangeOpenPair
          (show j ⁻¹ᵁ S ≤ j ⁻¹ᵁ T from fun _ hx => h hx)) (n+1) x) := by
  rw [← perfectSupportedChangeOpenKMap_eq_pullback (show j ⁻¹ᵁ S ≤ j ⁻¹ᵁ T from fun _ hx => h hx)
    (n+1)]
  exact qcqsPerfectSupportedOpenKEquiv_symm_changeOpen j h hS hT n x

end Quillen.Tests.SupportedOpenNaturality

namespace Quillen.Tests.SupportedOpenNaturality
open PerfectComplexes
variable {U X : Scheme.{u}} [CompactSpace X] (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The original supported relative K0 inclusion is bijective without compact opens. -/
theorem boundedFlat_original_KZero_lift (x : PerfectSupportedOpenK j T 0) :
    ∃! y : BoundedFlatPerfectSupportedOpenK j T 0,
      boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j T 0 y = x := by
  have hb := boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap_bijective j T 0
  obtain ⟨y, hy⟩ := hb.surjective x
  exact ⟨y, hy, fun z hz => hb.injective (hz.trans hy.symm)⟩

omit [CompactSpace X] in
/-- Fine supported classes retain the exact original relative comparison square. -/
theorem boundedFlat_original_changeWeak (n : ℕ) (x : BoundedFlatPerfectSupportedK T.ι n) :
    boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j T n
        (boundedFlatPerfectSupportedOpenKMap j T n x) =
      perfectSupportedOpenKMap j T n (boundedFlatPerfectSupportedToPerfectSupportedKMap T.ι n x) :=
  DFunLike.congr_fun (boundedFlatPerfectSupportedOpenToPerfectSupportedOpen_comp j T n) x

/-- Original relative App2 gives a literal supported factorization, not a derived substitute. -/
theorem boundedFlat_original_relative_factorization
    (K : (boundedFlatPerfectSupported T.ι).FullSubcategory)
    (L : (perfectSupported T.ι).FullSubcategory)
    (f : (boundedFlatPerfectSupportedInclusion T.ι).obj K ⟶ L) :
    ∃ M, ∃ i : K ⟶ M, ∃ p : (boundedFlatPerfectSupportedInclusion T.ι).obj M ⟶ L,
      (boundedFlatPerfectSupportedOpenWaldhausen j T).cof i ∧
      (perfectSupportedOpenWeakWaldhausen j T).weq p ∧
      (boundedFlatPerfectSupportedInclusion T.ι).map i ≫ p = f :=
  (boundedFlatPerfectSupportedOpenInclusion_approximation j T).lift f

end Quillen.Tests.SupportedOpenNaturality
