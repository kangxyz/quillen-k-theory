/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenUnitConeConstruction
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-!
# Construction of open restriction unit cones

Regression statements construct an injective replacement of a restricted
lower-bounded complex with quasicoherent homology and its global adjoint map.
They retain the cone's homology and lower bound, including the explicit shift
from cutoff `-7` to `-8`.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace QuillenTest.OpenUnitConeConstruction
local instance unitModelDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The actual injective model is constructed from the original input alone. -/
theorem original_model {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (K : CochainComplex X.Modules ℤ) (b : ℤ) [K.IsGE b]
    (hK : ∀ n, (K.homology n).IsQuasicoherent) :
    ∃ (I : CochainComplex U.Modules ℤ) (q : (restrict j).obj K ⟶ I),
      I.IsStrictlyGE b ∧ (∀ n, Injective (I.X n)) ∧ QuasiIso q ∧
      let C := CochainComplex.mappingCone ((restrictPushforwardComplexAdjunction j).homEquiv K I q)
      (∀ n, (C.homology n).IsQuasicoherent) ∧ C.IsGE (b-1) ∧
        IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj C)) :=
  exists_restrictionUnitCone_model j K b hK

/-- Constructed replacements give genuine chain maps into the literal ordinary direct image. -/
theorem original_global_map {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (K : CochainComplex X.Modules ℤ) (b : ℤ) [K.IsGE b]
    (hK : ∀ n, (K.homology n).IsQuasicoherent) :
    ∃ (I : CochainComplex U.Modules ℤ) (f : K ⟶ (pushforwardComplex j).obj I),
      (∀ n, Injective (I.X n)) ∧ QuasiIso ((restrict j).map f) ∧
      (∀ n, ((CochainComplex.mappingCone f).homology n).IsQuasicoherent) ∧
      (CochainComplex.mappingCone f).IsGE (b-1) := by
  obtain ⟨I,q,_,hi,hq,hC,hb,_⟩ := exists_restrictionUnitCone_model j K b hK
  let := hq
  exact ⟨I, (restrictPushforwardComplexAdjunction j).homEquiv K I q,
    hi, quasiIso_restrict_chain_adjoint j q, hC, hb⟩

/-- A negative original lower bound is retained with exactly one cone shift. -/
theorem negative_cutoff {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (K : CochainComplex X.Modules ℤ) [K.IsGE (-7)]
    (hK : ∀ n, (K.homology n).IsQuasicoherent) :
    ∃ (I : CochainComplex U.Modules ℤ) (f : K ⟶ (pushforwardComplex j).obj I),
      QuasiIso ((restrict j).map f) ∧ (CochainComplex.mappingCone f).IsGE (-8) := by
  obtain ⟨I,f,_,hq,_,hb⟩ := original_global_map j K (-7) hK
  exact ⟨I,f,hq,hb⟩

end QuillenTest.OpenUnitConeConstruction
