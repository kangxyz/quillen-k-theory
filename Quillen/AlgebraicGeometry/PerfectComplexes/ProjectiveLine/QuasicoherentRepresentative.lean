/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.BoundedQuasicoherentModels


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.Affine.InjectiveCounit
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Homology
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Pushforward.AffineBounded
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.InjectivePushforwardAdjunction
public import Quillen.Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.SheafSequence
public import Aglib.AlgebraicGeometry.Cohomology.Injective.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsGlobal
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.ChartAffineness
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Bounded quasicoherent sources for original affine injective counits -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace Quillen.PerfectComplexes.ProjectiveLine

attribute [local instance] qcRepresentativeStandard

open AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Pretriangulated
attribute [local instance] Abelian.hasFiniteBiproducts

open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.PolynomialLaurent

/-- Every original complex on the actual two-chart line with bounded QC
cohomology admits a constructed bounded termwise-QC model in the original
ambient derived category. No termwise QC hypothesis on the input is used. -/
theorem exists_bounded_quasicoherent_model (R : CommRingCat.{u})
    (K : CochainComplex (twoChartLine R).Modules ℤ) (a b : ℤ) (hab : a ≤ b) [K.IsGE a] [K.IsLE b]
    (hqc : ∀ i, (K.homology i).IsQuasicoherent) :
    ∃ P : CochainComplex (twoChartLine R).Modules ℤ, (∀ i, i < a ∨ b + 1 < i → IsZero (P.X i)) ∧
      (∀ i, (P.X i).IsQuasicoherent) ∧
        Nonempty ((DerivedCategory.Q).obj P ≅ (DerivedCategory.Q).obj K) := by
  have : QuasiIso (K.πTruncGE a) := (K.quasiIso_πTruncGE_iff a).mpr inferInstance
  obtain ⟨I, s, hs, hinj, hl⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (K.truncGE a) a
  let := hs
  let := hl
  let q := K.πTruncGE a ≫ s
  have : QuasiIso q := inferInstance
  have : I.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact (exactAt_iff_of_quasiIsoAt q i).mp (K.exactAt_of_isLE b i hi)
  have hIq (i : ℤ) : (I.homology i).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (twoChartLine R).ringCatSheaf).prop_of_iso
      (isoOfQuasiIsoAt q i) (hqc i)
  obtain ⟨P, hPb, hPq, ⟨eP⟩⟩ := exists_bounded_qc_model_of_twoAffine_injective
    (.of (Polynomial R)) (.of (Polynomial R)) (.of (LaurentPolynomial R))
    (laurentPlus R) (laurentMinus R) (plusChart R) (minusChart R)
    (chart_isPullback R) (charts_jointly_surjective R) I a b hab hinj hIq
  exact ⟨P, hPb, hPq, ⟨eP ≪≫ (asIso ((DerivedCategory.Q).map q)).symm⟩⟩

/-- An arbitrary intrinsic perfect bounded-below derived object on the actual
line has a genuine bounded-below termwise-QC representative. This is a producer,
not a supplied replacement premise. -/
theorem exists_quasicoherent_model_of_perfect_plus (R : CommRingCat.{u})
    (K : DerivedCategory.Plus (twoChartLine R).Modules)
    (hK : perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj K)) :
    ∃ P : CochainComplex.Plus (twoChartLine R).Modules,
      (∀ i, (P.obj.X i).IsQuasicoherent) ∧ Nonempty (DerivedCategory.Plus.Q.obj P ≅ K) := by
  obtain ⟨L, ⟨eL⟩⟩ :=
    (perfectDerivedObjects_iff_exists_representative (twoChartLine R) _).mp hK
  obtain ⟨c, b, hb⟩ := locallyPerfect_homology_bounded L.property
  let a := min c b
  have : L.obj.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (hb i (Or.inl (by dsimp [a] at hi; omega)))
  have : L.obj.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (hb i (Or.inr hi))
  obtain ⟨P, hPb, hPq, ⟨eP⟩⟩ := exists_bounded_quasicoherent_model R L.obj a b
    (min_le_right _ _) (locallyPerfect_quasicoherent_homology L.property)
  have : P.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).mpr
    (fun i hi => hPb i (Or.inl hi))
  let Pp : CochainComplex.Plus (twoChartLine R).Modules := ⟨P, a, inferInstance⟩
  exact ⟨Pp, hPq, ⟨DerivedCategory.Plus.ι.preimageIso (eP ≪≫ eL)⟩⟩

end Quillen.PerfectComplexes.ProjectiveLine
