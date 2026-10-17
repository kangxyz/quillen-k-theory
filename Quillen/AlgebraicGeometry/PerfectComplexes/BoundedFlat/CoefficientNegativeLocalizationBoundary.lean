/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientNegativeLocalizationExactness

/-!
# The fixed fine localization boundary on original negative groups

The original signed same-null cone boundary is transported through the actual
full-open comparison and the original negative-group comparisons. Explicit
integer reindexing gives the map from degree `-i` on the open to degree `-(i+1)`
with support. Both adjacent exactness statements use the original restriction
and support-forgetting maps. No comparison with the connective geometric
boundary or raw spectrum is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The same-null signed boundary, expressed on the actual fine full-open telescope. -/
def boundedFlatCoefficientFineLocalizationConnecting (a : Under R) (d : ℤ) :
    stableHomotopyGroup ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).obj a) (d + 1) ⟶
      stableHomotopyGroup ((boundedFlatCoefficientSupportedBassTelescopeFunctor f).obj a) d :=
  let := boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence f a
    (d + 1)
  inv ((stableHomotopyFunctor (d + 1)).map
    ((boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a)) ≫
      stableMappingConeConnecting ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
        (boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d

/-- The fixed full-open boundary is exact after the original telescope restriction. -/
theorem boundedFlatCoefficientFineLocalizationConnecting_exact_open (a : Under R) (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map
      ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a))
      (boundedFlatCoefficientFineLocalizationConnecting f a d) := by
  let H := stableHomotopyFunctor (d + 1)
  let c := H.map ((boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a)
  let : IsIso c :=
    boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence f a (d + 1)
  have hi : H.map (mappingConeInclusion
      ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)) ≫ c =
      H.map ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a) := by
    rw [← H.map_comp]
    exact congrArg H.map
      (boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_inclusion f a)
  have he := stableMappingConeConnecting_exact_cone
    ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
    (boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d
  intro y
  change stableMappingConeConnecting
    ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
    (boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d
      (inv c y) = 0 ↔ _
  rw [he]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hi, ConcreteCategory.comp_apply, hx]
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id c) y
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    rw [← hi, ConcreteCategory.comp_apply]
    exact (ConcreteCategory.congr_hom (IsIso.hom_inv_id c) _).symm

/-- The fixed boundary is exact before the original telescope support-forgetting map. -/
theorem boundedFlatCoefficientFineLocalizationConnecting_exact_supported
    (a : Under R) (d : ℤ) :
    Function.Exact (boundedFlatCoefficientFineLocalizationConnecting f a d)
      ((stableHomotopyFunctor d).map
        ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)) := by
  let c := (stableHomotopyFunctor (d + 1)).map
    ((boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a)
  let : IsIso c :=
    boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence f a (d + 1)
  have he := stableMappingConeConnecting_exact_source
    ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
    (boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d
  intro y
  rw [he]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨c z, ?_⟩
    change stableMappingConeConnecting
      ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
      (boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d
        (inv c (c z)) = y
    rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]
    exact hz
  · rintro ⟨z, hz⟩
    exact ⟨inv c z, hz⟩

/-- The explicit integer reindexing between adjacent original negative degrees. -/
def negativeLocalizationDegreeIso (i : ℕ) :
    stableHomotopyFunctor (-(i : ℤ)) ≅
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ) + 1) :=
  eqToIso (by congr 1; omega)

/-- The fixed signed boundary on the original negative groups, including K₀ to degree −1. -/
def boundedFlatCoefficientNegativeLocalizationConnecting (i : ℕ) (a : Under R) :
    (Bass.negativeKFunctor i).obj ((boundedFlatCoefficientQuasiCompactRow P).obj a) ⟶
      (Bass.supportedNegativeKFunctor (i + 1)).obj
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  exact (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a ≫
    (negativeLocalizationDegreeIso i).hom.app
      ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).obj a) ≫
    boundedFlatCoefficientFineLocalizationConnecting f a (-((i + 1 : ℕ) : ℤ)) ≫
    (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f (i + 1)).inv.app a

/-- The boundary followed by the original supported comparison is its specified signed formula. -/
@[reassoc]
theorem boundedFlatCoefficientNegativeLocalizationConnecting_comparison
    (i : ℕ) (a : Under R) :
    letI : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
    boundedFlatCoefficientNegativeLocalizationConnecting f i a ≫
      (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f (i + 1)).hom.app a =
    (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).obj a) ≫
      boundedFlatCoefficientFineLocalizationConnecting f a (-((i + 1 : ℕ) : ℤ)) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  simp only [boundedFlatCoefficientNegativeLocalizationConnecting, Category.assoc,
    Iso.inv_hom_id_app]
  exact congrArg (fun t =>
    (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).obj a) ≫ t)
    (Category.comp_id _)

/-- Exactness at the original open negative group, including the original open K₀ group. -/
theorem boundedFlatCoefficientNegativeLocalizationConnecting_exact_open
    (i : ℕ) (a : Under R) :
    Function.Exact ((boundedFlatCoefficientOriginalNegativeKRestriction f i).app a)
      (boundedFlatCoefficientNegativeLocalizationConnecting f i a) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  let eQ := (boundedFlatCoefficientAmbientNegativeKTelescopeComparison Q i).app a ≪≫
    (negativeLocalizationDegreeIso i).app
      ((boundedFlatCoefficientAmbientBassTelescopeFunctor Q).obj a)
  let eP := (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).app a ≪≫
    (negativeLocalizationDegreeIso i).app
      ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).obj a)
  let eS := (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f (i + 1)).app a
  have hr : (boundedFlatCoefficientOriginalNegativeKRestriction f i).app a ≫ eP.hom =
      eQ.hom ≫ (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ) + 1)).map
        ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a) := by
    have h0 : (boundedFlatCoefficientOriginalNegativeKRestriction f i).app a ≫
        (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a =
      (boundedFlatCoefficientAmbientNegativeKTelescopeComparison Q i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a) :=
      NatTrans.congr_app (boundedFlatCoefficientAmbientBassNegativeMap_fullOpen f i) a
    have h1 := (negativeLocalizationDegreeIso i).hom.naturality
      ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ (negativeLocalizationDegreeIso i).hom.app
        ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).obj a)) h0).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun t =>
              (boundedFlatCoefficientAmbientNegativeKTelescopeComparison Q i).hom.app a ≫ t)
              h1).trans (Category.assoc _ _ _).symm)))
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    eQ.addCommGroupIsoToAddEquiv eP.addCommGroupIsoToAddEquiv eS.addCommGroupIsoToAddEquiv
    (H := boundedFlatCoefficientFineLocalizationConnecting_exact_open f a
      (-((i + 1 : ℕ) : ℤ)))
  · ext x
    exact (ConcreteCategory.congr_hom hr x).symm
  · ext x
    exact (ConcreteCategory.congr_hom
      (boundedFlatCoefficientNegativeLocalizationConnecting_comparison f i a) x).symm

/-- Exactness at the original supported negative group after the fixed boundary. -/
theorem boundedFlatCoefficientNegativeLocalizationConnecting_exact_supported
    (i : ℕ) (a : Under R) :
    Function.Exact (boundedFlatCoefficientNegativeLocalizationConnecting f i a)
      ((Bass.supportedNegativeKForgetNat (i + 1)).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a)) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  let eP := (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).app a ≪≫
    (negativeLocalizationDegreeIso i).app
      ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).obj a)
  let eS := (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f (i + 1)).app a
  let eQ := (boundedFlatCoefficientAmbientNegativeKTelescopeComparison Q (i + 1)).app a
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    eP.addCommGroupIsoToAddEquiv eS.addCommGroupIsoToAddEquiv eQ.addCommGroupIsoToAddEquiv
    (H := boundedFlatCoefficientFineLocalizationConnecting_exact_supported f a
      (-((i + 1 : ℕ) : ℤ)))
  · ext x
    exact (ConcreteCategory.congr_hom
      (boundedFlatCoefficientNegativeLocalizationConnecting_comparison f i a) x).symm
  · ext x
    exact (ConcreteCategory.congr_hom
      (boundedFlatCoefficientSupportedNegativeKTelescopeComparison_forget_app f (i + 1) a) x).symm

end Quillen.PerfectComplexes
