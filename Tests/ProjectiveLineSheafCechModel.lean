/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.CechModel
public import Mathlib.Data.ZMod.Basic

/-! # Original sheaf Cech maps and strict-perfect models

The actual counits, signed cone differential and both chain homotopies are
retained. The base ring may be nonreduced or the zero ring.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open CochainComplex.HomComplex
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine Quillen.Scheme.PolynomialLaurent
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
namespace Quillen.Tests.ProjectiveLineSheafCechModel
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- The affine comparison uses the original counit naturality square. -/
theorem original_counit_square {A B : (Spec R).Modules} (f : A ⟶ B) :
    (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ B.fromTildeΓ =
      A.fromTildeΓ ≫ f :=
  Scheme.Modules.fromTildeΓNatTrans.naturality f

/-- The actual source counit, rather than a replacement arrow, has a right inverse. -/
theorem original_source_counit [M.IsQuasicoherent] :
    let S := (Scheme.Modules.pushforward (projection R)).obj
      ((openLocalization (plusChart R)).obj M ⨯ (openLocalization (minusChart R)).obj M)
    letI : IsIso S.fromTildeΓ := isIso_cechSourceCounit R M
    S.fromTildeΓ ≫ inv S.fromTildeΓ = 𝟙 _ := by
  have := isIso_cechSourceCounit R M
  exact IsIso.hom_inv_id _

/-- The actual overlap counit has the other inverse identity. -/
theorem original_overlap_counit [M.IsQuasicoherent] :
    let T := (Scheme.Modules.pushforward (projection R)).obj
      ((openLocalization (laurentPlus R ≫ plusChart R)).obj M)
    letI : IsIso T.fromTildeΓ := isIso_cechOverlapCounit R M
    inv T.fromTildeΓ ≫ T.fromTildeΓ = 𝟙 _ := by
  have := isIso_cechOverlapCounit R M
  exact IsIso.inv_hom_id _

/-- Negating the source coordinate cancels the literal minus-one shift sign. -/
theorem original_sheaf_differential :
    let d := (Scheme.Modules.pushforward (projection R)).map
      (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
        (plusChart R) (minusChart R) (overlap_equation R) M)
    let φ := (single (Spec R).Modules (.up ℤ) 0).map d;
    -(CochainComplex.mappingCone.inl φ).v 0 (-1) rfl ≫
        (originalSheafCechComplex R M).d 0 1 =
      d ≫ (CochainComplex.mappingCone.inr φ).f 0 := by
  intro d φ
  have h := CochainComplex.mappingCone.inl_v_d φ 0 (-1) 1 rfl rfl
  have hf : φ.f 0 = d := rfl
  rw [hf] at h
  simpa [originalSheafCechComplex, CochainComplex.shiftFunctor, φ, d,
    Preadditive.neg_comp, Preadditive.comp_neg, Cochain.neg_v] using h

/-- Both original chain maps and both homotopies land in an actual strict-perfect sheaf complex. -/
theorem original_chain_maps [IsFiniteLocallyFree (twoChartLine R) M] :
    ∃ P : StrictPerfect (Spec R),
      ∃ f : originalSheafCechComplex R M ⟶ P.obj,
      ∃ g : P.obj ⟶ originalSheafCechComplex R M,
      Nonempty (Homotopy (f ≫ g) (𝟙 _)) ∧ Nonempty (Homotopy (g ≫ f) (𝟙 _)) := by
  obtain ⟨P, ⟨h⟩⟩ := exists_strictSheafCech_model R M
  exact ⟨P, h.hom, h.inv, ⟨h.homotopyHomInvId⟩, ⟨h.homotopyInvHomId⟩⟩

/-- The actual forward chain map is a quasi-isomorphism. -/
theorem original_quasiIso [IsFiniteLocallyFree (twoChartLine R) M] :
    ∃ P : StrictPerfect (Spec R),
      ∃ f : originalSheafCechComplex R M ⟶ P.obj, QuasiIso f := by
  obtain ⟨P, ⟨h⟩⟩ := exists_strictSheafCech_model R M
  exact ⟨P, h.hom, h.quasiIso_hom⟩

/-- Nonreduced bases retain the actual sheaf complex and original homotopy equivalence. -/
theorem nonreduced_model (M : (twoChartLine (.of (ZMod 4))).Modules)
    [IsFiniteLocallyFree (twoChartLine (.of (ZMod 4))) M] :
    ∃ P : StrictPerfect (Spec (.of (ZMod 4))),
      Nonempty (HomotopyEquiv (originalSheafCechComplex (.of (ZMod 4)) M) P.obj) :=
  exists_strictSheafCech_model _ M

/-- The zero-ring geometry has the same original-map strict-perfect comparison. -/
theorem zero_ring_model (M : (twoChartLine (.of (ZMod 1))).Modules)
    [IsFiniteLocallyFree (twoChartLine (.of (ZMod 1))) M] :
    ∃ P : StrictPerfect (Spec (.of (ZMod 1))),
      Nonempty (HomotopyEquiv (originalSheafCechComplex (.of (ZMod 1)) M) P.obj) :=
  exists_strictSheafCech_model _ M

end Quillen.Tests.ProjectiveLineSheafCechModel
