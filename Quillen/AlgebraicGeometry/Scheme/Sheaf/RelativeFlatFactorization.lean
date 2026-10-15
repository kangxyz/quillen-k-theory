/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.RelativeProjectiveFactorization
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.BoundedFlatModels
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatExtensions

/-!
# Relative flat factorization of original sheaf-complex maps

Apply genuine relative projective factorization to the actual underlying
module-presheaf map, then exact sheafification and its original counits.
For a degreewise-flat source this constructs an actual short exact inclusion
with flat quotient followed by an actual sheaf quasi-isomorphism, retaining
the original commuting triangle and explicit upper bounds. The forgetful
functor to presheaves is not assumed exact.
-/
@[expose] public section
open Quillen
open Quillen.SchemeSheaf



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite HomologicalComplex
open Quillen.CochainComplex
namespace AlgebraicGeometry.Scheme.Modules

/-- Actual relative flat replacement for a map between bounded-above complexes.
The first map is an original short exact inclusion with flat quotient; the
second is an original sheaf quasi-isomorphism. -/
theorem exists_boundedAbove_relative_flat_factorization (X : Scheme.{u})
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b] (hK : ∀ n, stalkwiseFlat X (K.X n)) :
    ∃ (M Q : CochainComplex X.Modules ℤ) (i : K ⟶ M) (p : M ⟶ L)
      (q : M ⟶ Q) (w : i ≫ q = 0),
      QuasiIso p ∧ i ≫ p = f ∧ (ShortComplex.mk i q w).ShortExact ∧
      M.IsStrictlyLE (b + 1) ∧ Q.IsStrictlyLE (b + 1) ∧
      (∀ n, stalkwiseFlat X (M.X n)) ∧ ∀ n, stalkwiseFlat X (Q.X n) := by
  let R := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let A := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let RH : CochainComplex X.Modules ℤ ⥤
      CochainComplex (PresheafOfModules.{u} X.ringCatSheaf.obj) ℤ := R.mapHomologicalComplex (.up ℤ)
  let AH : CochainComplex (PresheafOfModules.{u} X.ringCatSheaf.obj) ℤ ⥤
      CochainComplex X.Modules ℤ := A.mapHomologicalComplex (.up ℤ)
  have hR (T : CochainComplex X.Modules ℤ) [T.IsStrictlyLE b] : (RH.obj T).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact R.map_isZero (T.isZero_of_isStrictlyLE b n hn)
  have := hR K
  have := hR L
  obtain ⟨M₀, i₀, p₀, hbM₀, hp₀, hfac, hi₀⟩ :=
    exists_boundedAbove_relative_projective_factorization (RH.map f) b
  have : Mono i₀ := HomologicalComplex.mono_of_mono_f _ (fun n => by
    let := (splitMono_projective_cokernel_of_op_epiWithInjectiveKernel (i₀.f n) (hi₀ n)).1
    infer_instance)
  let Q₀ := cokernel i₀
  let S₀ := ShortComplex.mk i₀ (cokernel.π i₀) (cokernel.condition i₀)
  have hs₀ : S₀.ShortExact := { exact := ShortComplex.cokernelSequence_exact i₀ }
  have hQ₀ (n : ℤ) : Projective (Q₀.X n) :=
    relative_factorization_projective_cokernel i₀ hi₀ n
  have hbQ₀ : Q₀.IsStrictlyLE (b + 1) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact IsZero.of_epi ((cokernel.π i₀).f n)
      (M₀.isZero_of_isStrictlyLE (b + 1) n hn)
  let M := AH.obj M₀
  let Q := AH.obj Q₀
  let eK := sheafificationComplexCounitIso X K
  let eL := sheafificationComplexCounitIso X L
  let i : K ⟶ M := eK.inv ≫ AH.map i₀
  let p : M ⟶ L := AH.map p₀ ≫ eL.hom
  let q : M ⟶ Q := AH.map (cokernel.π i₀)
  have w : i ≫ q = 0 := by
    dsimp [i, q]
    rw [Category.assoc, ← AH.map_comp, cokernel.condition, AH.map_zero, comp_zero]
  let S := ShortComplex.mk i q w
  have hS : S.ShortExact := by
    have hsA : (S₀.map AH).ShortExact := hs₀.map_of_exact AH
    apply ShortComplex.shortExact_of_iso (S₁ := S₀.map AH) (S₂ := S) _ hsA
    refine ShortComplex.isoMk (S₁ := S₀.map AH) (S₂ := S) eK (Iso.refl _) (Iso.refl _) ?_ ?_
    · dsimp [S₀, S, i]
      simp
    · dsimp [S₀, S, q]
      simp
  have hQ (n : ℤ) : stalkwiseFlat X (Q.X n) :=
    stalkwiseFlat_sheafify_projective X (Q₀.X n)
  have hM (n : ℤ) : stalkwiseFlat X (M.X n) :=
    stalkwiseFlat_middle_of_shortExact
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n) (hK n) (hQ n)
  refine ⟨M, Q, i, p, q, w, ?_, ?_, hS, ?_, ?_, hM, hQ⟩
  · let : QuasiIso p₀ := hp₀
    have : A.PreservesHomology := by dsimp [A]; infer_instance
    have : QuasiIso (AH.map p₀) := by
      exact HomologicalComplex.quasiIso_map_of_preservesHomology p₀ A
    dsimp [p]
    infer_instance
  · dsimp [i, p]
    rw [Category.assoc, ← AH.map_comp_assoc, hfac]
    have hn := sheafificationComplexCounitIso_naturality f
    change AH.map (RH.map f) ≫ eL.hom = eK.hom ≫ f at hn
    rw [hn]
    simp
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact A.map_isZero (M₀.isZero_of_isStrictlyLE (b + 1) n hn)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact A.map_isZero (Q₀.isZero_of_isStrictlyLE (b + 1) n hn)

end AlgebraicGeometry.Scheme.Modules
