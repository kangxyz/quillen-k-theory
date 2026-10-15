/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalStrictWeakImage

/-! # Unconditional original principal strict-image comparison consumers -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.StrictOpenWeakImage

open Quillen
open PerfectComplexes Waldhausen StrictOpenWeakImage
variable (R : CommRingCat.{u}) (r : R)

/-- Genuine geometry and the actual cone cylinder supply a strict source cofibration. -/
theorem actual_principal_cofibration_factorization
    {A : StrictPerfect (Spec R)} {B : StrictPerfect (Spec (.of (Localization.Away r)))}
    (f : (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj A ⟶
      B)
    (E : StrictPerfect (Spec R))
    (q : (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj E ⟶
      B)
    (hq : (strictWaldhausen _).weq q) :
    ∃ (M : StrictPerfect (Spec R)) (a : A ⟶ M)
      (p : (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj M
        ⟶ B),
      (strictWaldhausen (Spec R)).cof a ∧ (strictWaldhausen _).weq p ∧
        (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map a ≫
          p = f :=
  (principal_approximationOnImage R r).lift f ⟨E, q, hq⟩

/-- Relative weakness is precisely actual original restriction weakness. -/
theorem actual_relative_weak_iff {A B : StrictPerfect (Spec R)} (f : A ⟶ B) :
    (coarseWaldhausen (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).weq f ↔
      (strictWaldhausen _).weq ((strictRestrict
        (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map f) :=
        Iff.rfl

/-- The genuine inherited target preserves every displayed original pushout along a cofibration. -/
theorem actual_image_pushout {A B E Q : PrincipalObj R r}
    {i : A ⟶ B} {f : A ⟶ E} {g : B ⟶ Q} {j : E ⟶ Q}
    (hi : (principalWaldhausen R r).cof i) (hQ : IsPushout i f g j) :
    IsPushout i.hom f.hom g.hom j.hom := (principalInclusion_exact R r).pushout hi hQ

/-- All actual source-based homotopy maps of the original corestriction are bijective. -/
theorem actual_principal_homotopy_map
    (x : (coarseWaldhausen (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R
      r)).Delooping) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (deloopingMap (principalCorestrict_exact R r)).hom (x := x) rfl) :=
  (principal_deloopingMap_isWeakHomotopyEquivalence R r).homotopy_bijective x n

/-- Every actual image-category K class has a unique original relative preimage. -/
theorem unique_original_relative_preimage (n : ℕ) (y : (principalWaldhausen R r).K n) :
    ∃! x, KMap (principalCorestrict_exact R r) n x = y := by
  exact ⟨(principalKEquiv R r n).symm y, (principalKEquiv R r n).apply_symm_apply y,
    fun x hx ↦ (principalKEquiv R r n).injective (hx.trans ((principalKEquiv R r n).apply_symm_apply
      y).symm)⟩

/-- The comparison preserves the exact original map to strict-perfect K-theory on the open. -/
theorem inverse_relative_restriction (n : ℕ) (y : (principalWaldhausen R r).K n) :
    relativeKRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r) n
      ((principalKEquiv R r n).symm y) =
      KMap (principalInclusion_exact R r) n y := by
  rw [← DFunLike.congr_fun (principalInclusion_comp_corestrict R r n)
    ((principalKEquiv R r n).symm y), MonoidHom.comp_apply]
  exact congrArg (KMap (principalInclusion_exact R r) n) ((principalKEquiv R r n).apply_symm_apply
    y)

/-- Even after changing weak classes and corestricting, the full composite is original strict
  restriction. -/
theorem original_fine_restriction_composite (n : ℕ) :
    (KMap (principalInclusion_exact R r) n).comp
      ((principalKEquiv R r n).toMonoidHom.comp
        (KMap (Fibration.changeWeak_exact (nested
          (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))) n)) =
      strictKRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r) n := by
  ext x
  exact (DFunLike.congr_fun (principalInclusion_comp_corestrict R r n)
    (KMap (Fibration.changeWeak_exact (nested
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))) n x)).trans
      (DFunLike.congr_fun (relativeKRestrict_comp_changeWeak
        (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r) n)
        x)

end QuillenTest.StrictOpenWeakImage
