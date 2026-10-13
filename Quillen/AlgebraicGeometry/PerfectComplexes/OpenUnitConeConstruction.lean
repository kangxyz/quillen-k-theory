/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenRestrictionUnitCone
/-! # Constructing the genuine supported restriction-unit cone

A lower-bounded original QC-homology complex supplies an actual injective
replacement of its open restriction. Good truncation and the genuine injective
resolution construct the local map; no model, target-QC or cone premise is supplied.
The original chain-adjoint cone has QC homology, lower bound b-1, and zero
original derived restriction. Its perfection is not asserted.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
/-- The standard upper-universe derived category used to construct injective unit-cone models. -/
local instance unitConstructionDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- Construct an actual injective replacement and original supported unit cone,
without supplying an injective model or a QC target premise. -/
lemma exists_restrictionUnitCone_model {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (K : Complex X) (b : ℤ) [K.IsGE b]
    (hK : ∀ n, (K.homology n).IsQuasicoherent) :
    ∃ (I : Complex U) (q : (restrict j).obj K ⟶ I),
      I.IsStrictlyGE b ∧ (∀ n, Injective (I.X n)) ∧ QuasiIso q ∧
      let C := CochainComplex.mappingCone ((restrictPushforwardComplexAdjunction j).homEquiv K I q)
      (∀ n, (C.homology n).IsQuasicoherent) ∧ C.IsGE (b-1) ∧
        IsZero ((toDerived U).obj ((restrict j).obj C)) := by
  let E := (restrict j).obj K
  have : E.IsGE b := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    exact ((Scheme.Modules.restrictFunctor j).map_isZero
      (K.exactAt_of_isGE b n hn).isZero_homology).of_iso (restrictHomologyIso j K n)
  have : QuasiIso (E.πTruncGE b) := (E.quasiIso_πTruncGE_iff b).mpr inferInstance
  obtain ⟨I,s,hs,hi,hb⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (E.truncGE b) b
  let := hs
  let := hb
  let q : (restrict j).obj K ⟶ I := E.πTruncGE b ≫ s
  have hq : QuasiIso q := by dsimp only [q]; infer_instance
  have hbound : ∀ n, n < b → IsZero (I.X n) := fun n hn => (CochainComplex.isStrictlyGE_iff I b).mp
    hb n hn
  have hp := restrictionUnitCone_properties j K I b b hbound hi hK q
  refine ⟨I, q, hb, hi, hq, hp.1, ?_, hp.2.2⟩
  simpa only [min_eq_left (show b-1 ≤ b by omega)] using hp.2.1

end Quillen.PerfectComplexes
