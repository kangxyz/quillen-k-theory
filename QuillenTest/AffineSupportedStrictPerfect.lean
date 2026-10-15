/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedStrictPerfectKEquivalence

/-!
Semantic consumers of the original supported affine strict-perfect comparison.
-/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.PerfectComplexes.Affine
attribute [local instance] Abelian.hasFiniteBiproducts
namespace QuillenTest.AffineSupportedStrictPerfect

open Quillen

/-- Degree zero is an equivalence of the original supported groups for an
arbitrary open, not only a positive-degree cofinality conclusion. -/
theorem original_supported_zero (R : CommRingCat.{u}) {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] (y : PerfectSupportedK j 0) :
    ∃! x : StrictSupportedK j 0, strictSupportedToPerfectKMap j 0 x = y := by
  obtain ⟨x, hx⟩ := (strictSupportedToPerfectKMap_bijective R j 0).2 y
  exact ⟨x, hx, fun x' hx' => (strictSupportedToPerfectKMap_bijective R j 0).1 (hx'.trans hx.symm)⟩

/-- Both inverse equations concern the original supported comparison map. -/
theorem original_supported_inverse (R : CommRingCat.{u}) {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] (n : ℕ) :
    ∃ g : PerfectSupportedK j n →* StrictSupportedK j n,
      g.comp (strictSupportedToPerfectKMap j n) = MonoidHom.id _ ∧
      (strictSupportedToPerfectKMap j n).comp g = MonoidHom.id _ := by
  let e := strictSupportedToPerfectKEquiv R j n
  refine ⟨e.symm.toMonoidHom, ?_, ?_⟩
  · ext x
    exact e.symm_apply_apply x
  · ext x
    exact e.apply_symm_apply x

/-- The geometric source, middle, and both literal kernels remain supported,
while both original triangles retain their exact chain maps. -/
theorem actual_supported_factorization (R : CommRingCat.{u}) {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j]
    (P : (strictSupported j).FullSubcategory) (B B' : Complex (Spec R))
    (hB' : perfectSupported j B') (w : P.obj ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : (strictSupported j).FullSubcategory) (D : Complex (Spec R))
      (c : C.obj ⟶ P.obj) (d : D ⟶ B) (u : C.obj ⟶ D) (v : B' ⟶ D),
      perfectSupported j D ∧ u ≫ d = c ≫ w ∧ v ≫ d = b ∧
      (∀ n, IsIso (homologyMap v n)) ∧
      ((restrict j).obj (kernel c)).Acyclic ∧ ((restrict j).obj (kernel d)).Acyclic := by
  obtain ⟨C, D, c, d, u, v, hD, hu, hv, hs, he, hc, hd, hkc, hkd⟩ :=
    exists_supported_strict_dual_factorization R j P B B' hB' w b
  exact ⟨C, D, c, d, u, v, hD, hs, he, fun _ => inferInstance, hkc.2, hkd.2⟩

/-- Actual supported epi kernels restrict to zero homology in every degree,
on every scheme, with no affine or split-epi premise. -/
theorem original_kernel_support {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K L : Complex X} (hK : perfectSupported j K) (hL : perfectSupported j L)
    (f : K ⟶ L) [Epi f] (n : ℤ) :
    IsZero (((restrict j).obj (kernel f)).homology n) :=
  (exactAt_iff_isZero_homology _ _).mp ((perfectSupported_kernel_of_epi j hK hL f).2 n)

/-- Applying the supported equivalence and then forgetting support gives
exactly the unchanged original absolute comparison of the same class. -/
theorem original_inclusion_square (R : CommRingCat.{u}) {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] (n : ℕ) (x : StrictSupportedK j n) :
    perfectSupportedKMap j n (strictSupportedToPerfectKEquiv R j n x) =
      strictToPerfectKMap (Spec R) n (strictSupportedKMap j n x) :=
  DFunLike.congr_fun (strictSupportedToPerfectKMap_inclusion j n) x

/-- The zero ring and its empty spectrum are included in the original
supported comparison without a nontriviality or nonempty-cover assumption. -/
theorem zero_ring_supported_comparison (n : ℕ) :
    Function.Bijective (strictSupportedToPerfectKMap
      (𝟙 (Spec (CommRingCat.of (ZMod 1)))) n) :=
  strictSupportedToPerfectKMap_bijective (CommRingCat.of (ZMod 1)) _ n

end QuillenTest.AffineSupportedStrictPerfect
