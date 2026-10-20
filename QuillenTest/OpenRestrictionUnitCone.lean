/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.OpenRestrictionUnitCone
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-!
# Open restriction unit cone regression statements

Records quasicoherent homology and the shifted lower bound of mapping cones,
then applies them to the literal cone of a restriction-pushforward adjoint map.
Separate statements retain the support vanishing and combine these properties
for a local quasi-isomorphism into a lower-bounded injective complex.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace QuillenTest.OpenRestrictionUnitCone
/-- Use the standard derived-category model in these comparison tests. -/
local instance testsConeDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The original cone has QC homology without termwise QC or boundedness. -/
theorem original_cone {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (hK : ∀ n, (K.homology n).IsQuasicoherent)
    (hL : ∀ n, (L.homology n).IsQuasicoherent) (n : ℤ) :
    ((CochainComplex.mappingCone f).homology n).IsQuasicoherent :=
  quasicoherent_homology_mappingCone f hK hL n

/-- Unequal input lower bounds retain the correct cone shift. -/
theorem shifted_bound {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (a b : ℤ) [K.IsGE a] [L.IsGE b] :
    (CochainComplex.mappingCone f).IsGE (min (a-1) b) := mappingCone_isGE f a b

/-- QC is proved for the literal cone of the original chain adjoint. -/
theorem original_unit_qc {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (K : CochainComplex X.Modules ℤ)
      (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hb : ∀ n, n < a → IsZero (I.X n)) (hi : ∀ n, Injective (I.X n))
    (hK : ∀ n, (K.homology n).IsQuasicoherent)
    (hI : ∀ n, (I.homology n).IsQuasicoherent)
    (q : (restrict j).obj K ⟶ I) (n : ℤ) :
    ((CochainComplex.mappingCone
      ((restrictPushforwardComplexAdjunction j).homEquiv K I q)).homology n).IsQuasicoherent :=
  quasicoherent_homology_restrictionUnitCone j K I a hb hi hK hI q n

/-- Actual support vanishing does not assume injectives, QC or compactness. -/
theorem original_unit_support {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (K : CochainComplex X.Modules ℤ) (I : CochainComplex U.Modules ℤ)
    (q : (restrict j).obj K ⟶ I) [QuasiIso q] :
    IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj (CochainComplex.mappingCone
      ((restrictPushforwardComplexAdjunction j).homEquiv K I q)))) :=
  isZero_restrict_restrictionUnitCone j K I q

/-- The original unit cone retains its explicit lower bound even without injectivity. -/
theorem original_unit_bound {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (K : CochainComplex X.Modules ℤ) (I : CochainComplex U.Modules ℤ) (a b : ℤ)
    (hb : ∀ n, n < a → IsZero (I.X n)) [K.IsGE b]
    (q : (restrict j).obj K ⟶ I) :
    (CochainComplex.mappingCone ((restrictPushforwardComplexAdjunction j).homEquiv K I q)).IsGE
      (min (b-1) a) := restrictionUnitCone_isGE j K I a b hb q

/-- No target-QC premise is needed for a genuine original local replacement. -/
theorem actual_replacement {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (K : CochainComplex X.Modules ℤ)
      (I : CochainComplex U.Modules ℤ) (a b : ℤ)
    (hb : ∀ n, n < a → IsZero (I.X n)) (hi : ∀ n, Injective (I.X n))
    (hK : ∀ n, (K.homology n).IsQuasicoherent) [K.IsGE b]
    (q : (restrict j).obj K ⟶ I) [QuasiIso q] :
    let C := CochainComplex.mappingCone ((restrictPushforwardComplexAdjunction j).homEquiv K I q)
    (∀ n, (C.homology n).IsQuasicoherent) ∧ C.IsGE (min (b-1) a) ∧
      IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj C)) :=
  restrictionUnitCone_properties j K I a b hb hi hK q

end QuillenTest.OpenRestrictionUnitCone
