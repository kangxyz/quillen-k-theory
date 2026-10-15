/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedHom.LocalModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SchemeDerivedHomVanishing

/-! # Genuine uniform low-single Hom vanishing for compact semi-separated schemes -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard
variable {X : Scheme.{u}}

/-- A finite family of actual affine strict models gives the explicit low-single
bound. The target sheaf may be any quasicoherent module, with no projectivity. -/
theorem derivedHom_single_eq_zero_of_finite_affine_models
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (E : Complex X) (s : Finset X.Opens) (b : ℤ) (hs : s.sup id = ⊤)
    (hmodels : ∀ U ∈ s, IsAffineOpen U ∧ ∃ P : Complex U.toScheme,
      strictPerfect U.toScheme P ∧ (∀ i, i < b → IsZero (P.X i)) ∧
      Nonempty ((toDerived U.toScheme).obj ((restrict U.ι).obj E) ≅ (toDerived U.toScheme).obj P))
    (M : X.Modules) [M.IsQuasicoherent] (a : ℤ) (ha : a ≤ b - (s.card : ℤ))
    (φ : (toDerived X).obj E ⟶
      (toDerived X).obj ((CochainComplex.singleFunctor X.Modules a).obj M)) : φ = 0 := by
  classical
  let L := (CochainComplex.singleFunctor X.Modules a).obj M
  let B : Set X.Opens := {V | IsAffineOpen V ∧ ∃ U ∈ s, V ≤ U}
  have hB : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V ∈ B := by
    intro U hU V hV
    obtain ⟨Z, hZ, hUZ⟩ := hU.2
    exact ⟨hU.1.inf hV.1, Z, hZ, inf_le_left.trans hUZ⟩
  have hlocal : ∀ V ∈ B, ∀ n : ℤ, n < b-a → DerivedHomZeroOn E L V n := by
    intro V hV n hn
    obtain ⟨U, hUs, hVU⟩ := hV.2
    obtain ⟨_, P, hP, hPb, ⟨eP⟩⟩ := hmodels U hUs
    let : IsAffine V.toScheme := hV.1
    let j := X.homOfLE hVU
    let Q := (restrict j).obj P
    let e : (toDerived V.toScheme).obj ((restrict V.ι).obj E) ≅ (toDerived V.toScheme).obj Q :=
      ((toDerived V.toScheme).mapIso (restrictOpenInclusionIso hVU E)).symm ≪≫
        restrictDerivedIso j eP
    let M' := (Scheme.Modules.restrictFunctor V.ι).obj M
    let eM : (toDerived V.toScheme).obj ((restrict V.ι).obj L) ≅
        (toDerived V.toScheme).obj ((CochainComplex.singleFunctor V.toScheme.Modules a).obj M') :=
      (toDerived V.toScheme).mapIso
        (((Scheme.Modules.restrictFunctor V.ι).mapCochainComplexSingleFunctor a).app M)
    exact hom_eq_zero_of_iso ((shiftFunctor (Derived V.toScheme) n).mapIso e) eM
      (strictPerfect_derivedHom_single_shift_eq_zero_of_isAffine V.toScheme Q
        (strictPerfect_restrict j hP) M' a b n
        (fun i hi => (Scheme.Modules.restrictFunctor j).map_isZero (hPb i hi)) (by omega))
  have hsin : ∀ U ∈ s, U ∈ B := fun U hU => ⟨(hmodels U hU).1, U, hU, le_rfl⟩
  have htop := derivedHomZeroOn_finite_union E L B hB (b-a) hlocal s hsin 0 (by omega)
  rw [hs] at htop
  have hz := htop (((shiftFunctorZero (Derived (⊤ : X.Opens).toScheme) ℤ).app
    ((toDerived (⊤ : X.Opens).toScheme).obj ((restrict (⊤ : X.Opens).ι).obj E))).hom ≫
      restrictDerivedHom (⊤ : X.Opens).ι φ)
  have hφ : restrictDerivedHom (⊤ : X.Opens).ι φ = 0 := by
    apply (cancel_epi (((shiftFunctorZero (Derived (⊤ : X.Opens).toScheme) ℤ).app
      ((toDerived (⊤ : X.Opens).toScheme).obj ((restrict (⊤ : X.Opens).ι).obj E))).hom)).mp
    simpa only [comp_zero] using hz
  let : IsIso (⊤ : X.Opens).ι := X.topIso.isIso_hom
  exact (restrictDerivedHom_eq_zero_iff (⊤ : X.Opens).ι φ).mp hφ

/-- Actual compactness, local strict models, affine intersection geometry and
Mayer–Vietoris produce a single uniform cutoff for all quasicoherent singles. -/
theorem locallyPerfect_exists_uniform_low_single_vanishing [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (E : Complex X) (hE : locallyPerfect X E) :
    ∃ c : ℤ, ∀ (M : X.Modules) [M.IsQuasicoherent], ∀ a : ℤ, a ≤ c →
      ∀ φ : (toDerived X).obj E ⟶
        (toDerived X).obj ((CochainComplex.singleFunctor X.Modules a).obj M), φ = 0 := by
  obtain ⟨s, b, hs, hmodels⟩ := locallyPerfect_exists_finite_affine_strict_lower_models hE
  exact ⟨b - (s.card : ℤ), fun M _ a ha =>
    derivedHom_single_eq_zero_of_finite_affine_models E s b hs hmodels M a ha⟩

end Quillen.PerfectComplexes
