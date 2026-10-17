/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientFullOpenBassRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedNegativeTelescopeForget

/-!
# Middle localization exactness for the original Bass negative groups

For an open immersion with compact source and qcqs ambient scheme, the original
supported negative-group forget map followed by the original scheme pullback is
exact at the ambient group, in every nonpositive degree including degree zero.
The proof transports the genuine same-null fine telescope cone sequence through
the actual supported and ambient comparison isomorphisms. No new boundary is
defined, and no surjectivity onto the open group is asserted.
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

/-- The original same-null fine localization maps are exact at the ambient telescope group. -/
theorem boundedFlatCoefficientSupportedBassTelescope_fullOpen_exact
    (a : Under R) (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a))
      ((stableHomotopyFunctor d).map
        ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)) := by
  let H := stableHomotopyFunctor d
  let j := (boundedFlatCoefficientSupportedBassTelescopeForget f).app a
  let c := (boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a
  let : IsIso (H.map c) :=
    boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence f a d
  have hb := stableMappingCone_exact_target j
    (boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d
  have he := hb.comp_injective (H.map c)
    (ConcreteCategory.bijective_of_isIso (H.map c)).injective (map_zero (H.map c).hom)
  have hc : H.map (mappingConeInclusion j) ≫ H.map c =
      H.map ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a) := by
    rw [← H.map_comp]
    exact congrArg H.map
      (boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_inclusion f a)
  change Function.Exact (H.map j)
    (H.map ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a))
  rw [← hc]
  exact he

/-- Original supported negative classes are precisely the kernel of original open pullback.
This includes the original supported K₀ image statement when `i = 0`.
-/
theorem boundedFlatCoefficientSupportedNegativeK_localization_exact
    (i : ℕ) (a : Under R) :
    Function.Exact
      ((Bass.supportedNegativeKForgetNat i).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a))
      ((boundedFlatCoefficientOriginalNegativeKRestriction f i).app a) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  let H := stableHomotopyFunctor (-(i : ℤ))
  let eS := (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f i).app a
  let eQ := (boundedFlatCoefficientAmbientNegativeKTelescopeComparison Q i).app a
  let eP := (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).app a
  let j := (Bass.supportedNegativeKForgetNat i).app
    ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a)
  let r := (boundedFlatCoefficientOriginalNegativeKRestriction f i).app a
  let j' := H.map ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
  let r' := H.map ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
  have hj : j ≫ eQ.hom = eS.hom ≫ j' :=
    boundedFlatCoefficientSupportedNegativeKTelescopeComparison_forget_app f i a
  have hr : r ≫ eP.hom = eQ.hom ≫ r' :=
    NatTrans.congr_app (boundedFlatCoefficientAmbientBassNegativeMap_fullOpen f i) a
  have he : Function.Exact j' r' :=
    boundedFlatCoefficientSupportedBassTelescope_fullOpen_exact f a (-(i : ℤ))
  change Function.Exact j r
  intro y
  constructor
  · intro hy
    have hy' : r' (eQ.hom y) = 0 := by
      calc
        _ = eP.hom (r y) := (ConcreteCategory.congr_hom hr y).symm
        _ = 0 := by rw [hy, map_zero]
    obtain ⟨z, hz⟩ := (he (eQ.hom y)).mp hy'
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso eS.hom).surjective z
    refine ⟨x, (ConcreteCategory.bijective_of_isIso eQ.hom).injective ?_⟩
    exact (ConcreteCategory.congr_hom hj x).trans hz
  · rintro ⟨x, rfl⟩
    apply (ConcreteCategory.bijective_of_isIso eP.hom).injective
    calc
      _ = r' (eQ.hom (j x)) := ConcreteCategory.congr_hom hr (j x)
      _ = r' (j' (eS.hom x)) :=
        congrArg r' (ConcreteCategory.congr_hom hj x)
      _ = 0 := he.apply_apply_eq_zero _
      _ = eP.hom 0 := (map_zero eP.hom.hom).symm

/-- At degree zero this is the original supported K₀ image, without open surjectivity. -/
theorem boundedFlatCoefficientSupportedKZero_localization_exact (a : Under R) :
    Function.Exact
      (Bass.supportedKZeroForget.app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a))
      (Bass.perfectKZeroFunctor.map
        ((boundedFlatCoefficientQuasiCompactRowRestriction f).app a)) :=
  boundedFlatCoefficientSupportedNegativeK_localization_exact f 0 a

end Quillen.PerfectComplexes
