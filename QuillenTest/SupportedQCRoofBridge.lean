/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.OneChartRoofs
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
/-!
# From supported quasicoherent factorizations to roofs

Records the passage from supported quasicoherent factorizations to denominators
and derived roofs, together with denominator formulas for locally zero or equal
maps. The final statements instantiate the roof property for a cover by a
compact open and an affine chart.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes.OpenDerivedImage
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace QuillenTest.SupportedQCRoofBridge
local instance bridgeTestDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- Supported factorization gives an actual source denominator through the original cocone. -/
theorem factorization_to_denominator {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : HasSupportedQCFactorizations j) : HasSupportedQCDenominators j :=
  hasSupportedQCDenominators_of_factorizations j h

/-- The bridge retains both actual original chain arrows and the original local derived square. -/
theorem original_roof {U X : Scheme.{u}} [CompactSpace X] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (h : HasSupportedQCDenominators j)
    (A P : CochainComplex X.Modules ℤ) (hA : locallyPerfect X A) (hP : locallyPerfect X P)
    (α : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj A) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P)) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A) (a : M ⟶ P), locallyPerfect X M ∧
      QuasiIso ((restrict j).map q) ∧
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) ≫ α =
        (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map a) :=
  hasDerivedRoofs_of_supportedQCDenominators j h A P hA hP α

/-- A lower-bounded QC target need not itself vanish on the open. -/
theorem original_local_null {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (h : HasSupportedQCDenominators j)
    {A B : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (α : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B)
      (hz : restrictDerivedHom j α = 0) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A), locallyPerfect X M ∧
      QuasiIso ((restrict j).map q) ∧ (DerivedCategory.Q (C := X.Modules)).map q ≫ α = 0 :=
  exists_denominator_of_restrictDerivedHom_zero j h hA b hB α hz

/-- The same actual denominator equalizes both original maps. -/
theorem original_local_equality {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (h : HasSupportedQCDenominators j)
    {A B : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (α β : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B)
    (heq : restrictDerivedHom j α = restrictDerivedHom j β) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A), locallyPerfect X M ∧
      QuasiIso ((restrict j).map q) ∧ (DerivedCategory.Q (C := X.Modules)).map q ≫ α =
        (DerivedCategory.Q (C := X.Modules)).map q ≫ β :=
  exists_denominator_of_restrictDerivedHom_eq j h hA b hB α β heq

/-- Actual one-chart geometry discharges the complete roof premise; X need not be affine. -/
theorem original_one_chart_roofs (R : CommRingCat.{u}) {U X : Scheme.{u}}
    [QuasiSeparatedSpace X] [CompactSpace U] (j : U ⟶ X) (k : Spec R ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) : HasDerivedRoofs j :=
  oneChart_hasDerivedRoofs R j k hcover

/-- A chart need not be presented literally as Spec, and the original open remains unchanged. -/
theorem original_affine_chart_roofs {U V X : Scheme.{u}}
    [QuasiSeparatedSpace X] [CompactSpace U] [IsAffine V]
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) : HasDerivedRoofs j :=
  affineChart_hasDerivedRoofs j k hcover

end QuillenTest.SupportedQCRoofBridge
