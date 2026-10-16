/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Restriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedZero
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Actual vanishing on unions of support opens -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard

lemma isZero_restrict_sup_iff {X : Scheme.{u}} (U T : X.Opens) (A : CochainComplex X.Modules ℤ) :
    IsZero ((DerivedCategory.Q (C := (U ⊔ T).toScheme.Modules)).obj ((restrict (U ⊔ T).ι).obj A)) ↔
      IsZero ((DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj A)) ∧
        IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj A)) := by
  let j := X.homOfLE (le_sup_left : U ≤ U ⊔ T)
  let k := X.homOfLE (le_sup_right : T ≤ U ⊔ T)
  let cU : restrict (U ⊔ T).ι ⋙ restrict j ≅ restrict U.ι :=
    restrictCompIso j (U ⊔ T).ι ≪≫ eqToIso (restrict_congr (Scheme.homOfLE_ι X le_sup_left))
  let cT : restrict (U ⊔ T).ι ⋙ restrict k ≅ restrict T.ι :=
    restrictCompIso k (U ⊔ T).ι ≪≫ eqToIso (restrict_congr (Scheme.homOfLE_ι X le_sup_right))
  constructor
  · intro h
    exact ⟨(isZero_toDerived_restrict_of_isZero j h).of_iso
      ((DerivedCategory.Q (C := U.toScheme.Modules)).mapIso (cU.app
      A)).symm,
      (isZero_toDerived_restrict_of_isZero k h).of_iso
        ((DerivedCategory.Q (C := T.toScheme.Modules)).mapIso (cT.app
        A)).symm⟩
  · rintro ⟨hU,hT⟩
    let V : Bool → Scheme.{u} := fun t => if t then U.toScheme else T.toScheme
    let f : ∀ t, V t ⟶ (U ⊔ T).toScheme := fun t => by
      cases t
      · exact k
      · exact j
    have : ∀ t, IsOpenImmersion (f t) := by intro t; cases t <;> dsimp [f] <;> infer_instance
    apply isZero_toDerived_of_openImmersionCover _ V f
    · intro x
      rcases x.property with hx | hx
      · exact ⟨true, ⟨x.val,hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩
      · exact ⟨false, ⟨x.val,hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩
    · intro t
      cases t
      · exact hT.of_iso ((DerivedCategory.Q (C := T.toScheme.Modules)).mapIso (cT.app A))
      · exact hU.of_iso ((DerivedCategory.Q (C := U.toScheme.Modules)).mapIso (cU.app A))

lemma restrictAcyclic_sup_iff {X : Scheme.{u}} (U T : X.Opens) (A : CochainComplex X.Modules ℤ) :
    ((restrict (U ⊔ T).ι).obj A).Acyclic ↔
      ((restrict U.ι).obj A).Acyclic ∧ ((restrict T.ι).obj A).Acyclic := by
  simpa only [isZero_toDerived_iff_acyclic] using isZero_restrict_sup_iff U T A

lemma restrictAcyclic_opensRange_iff {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : CochainComplex X.Modules ℤ) :
    ((restrict j.opensRange.ι).obj A).Acyclic ↔ ((restrict j).obj A).Acyclic := by
  rw [← isZero_toDerived_iff_acyclic, ← isZero_toDerived_iff_acyclic,
    ← isZero_toDerived_restrict_iff_of_isIso j.isoOpensRange.hom]
  let c : restrict j.opensRange.ι ⋙ restrict j.isoOpensRange.hom ≅ restrict j :=
    restrictCompIso _ _ ≪≫ eqToIso (restrict_congr j.isoOpensRange_hom_ι)
  exact ((DerivedCategory.Q (C := U.Modules)).mapIso (c.app A)).isZero_iff

lemma perfectSupported_sup_opensRange_iff {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : X.Opens) (A : CochainComplex X.Modules ℤ) :
    perfectSupported (T ⊔ j.opensRange).ι A ↔
      perfectSupported T.ι A ∧ ((restrict j).obj A).Acyclic := by
  change (locallyPerfect X A ∧ _) ↔ (locallyPerfect X A ∧ _) ∧ _
  rw [restrictAcyclic_sup_iff, restrictAcyclic_opensRange_iff]
  tauto

end Quillen.PerfectComplexes
