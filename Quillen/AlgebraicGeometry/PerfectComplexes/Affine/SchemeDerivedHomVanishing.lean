/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRestrictionIso
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedHomVanishing
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
/-!
# Presentation-independent affine derived Hom vanishing

Transport through the actual canonical spectrum isomorphism proves the
strict-source Hom-vanishing bound on every affine scheme without a supplied
presentation. Original lower term support and the exact shifted inequality
are retained, and the quasicoherent target single needs no projectivity.
A genuine supplied strict derived model also handles an arbitrary original
ambient source. Zero reflection uses the actual isomorphism restriction.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes

/-- Any affine scheme admits the actual strict-source vanishing theorem with its exact term bound.
-/
lemma strictPerfect_derivedHom_single_shift_eq_zero_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (P : CochainComplex X.Modules ℤ) (hP : strictPerfect X P) (M : X.Modules) [M.IsQuasicoherent]
    (a b n : ℤ) (hbound : ∀ i, i < b → IsZero (P.X i)) (hab : a + n < b)
    (φ : ((DerivedCategory.Q (C := X.Modules)).obj P)⟦n⟧ ⟶
      (DerivedCategory.Q (C := X.Modules)).obj ((_root_.CochainComplex.singleFunctor X.Modules
        a).obj M)) : φ = 0 := by
  let R := Γ(X, ⊤)
  let j : Spec R ⟶ X := X.isoSpec.inv
  let eP := ((DerivedCategory.Q (C := X.Modules)).commShiftIso n).app P
  let ψ := eP.hom ≫ φ
  let M' := (Scheme.Modules.restrictFunctor j).obj M
  let eM := (DerivedCategory.Q (C := (Spec R).Modules)).mapIso
    (((Scheme.Modules.restrictFunctor j).mapCochainComplexSingleFunctor a).app M)
  have hz := Affine.strictPerfect_derivedHom_single_eq_zero R ((restrict j).obj (P⟦n⟧))
    (strictPerfect_restrict j (strictPerfect_shift hP n)) M' a (b-n)
    (fun i hi => (Scheme.Modules.restrictFunctor j).map_isZero
      ((hbound (i+n) (by omega)).of_iso (P.shiftFunctorObjXIso n i (i+n) rfl)))
    (by omega) (restrictDerivedHom j ψ ≫ eM.hom)
  have hz' : restrictDerivedHom j ψ = 0 := by
    apply (cancel_mono eM.hom).mp
    simpa only [zero_comp] using hz
  have hψ : ψ = 0 := (restrictDerivedHom_eq_zero_iff j ψ).mp hz'
  apply (cancel_epi eP.hom).mp
  simpa only [comp_zero] using hψ

/-- A genuine strict derived model may replace arbitrary original terms on an affine scheme. -/
lemma derivedHom_single_shift_eq_zero_of_affine_strict_model (X : Scheme.{u}) [IsAffine X]
    (E : DerivedCategory X.Modules) (P : CochainComplex X.Modules ℤ) (hP : strictPerfect X P)
    (e : (DerivedCategory.Q (C := X.Modules)).obj P ≅ E) (M : X.Modules) [M.IsQuasicoherent]
    (a b n : ℤ) (hbound : ∀ i, i < b → IsZero (P.X i)) (hab : a + n < b)
    (φ : E⟦n⟧ ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((_root_.CochainComplex.singleFunctor X.Modules a).obj M)) :
    φ = 0 := by
  let e' := (shiftFunctor (DerivedCategory X.Modules) n).mapIso e
  have hz := strictPerfect_derivedHom_single_shift_eq_zero_of_isAffine X P hP M a b n hbound hab
    (e'.hom ≫ φ)
  apply (cancel_epi e'.hom).mp
  simpa only [comp_zero] using hz

end Quillen.PerfectComplexes
