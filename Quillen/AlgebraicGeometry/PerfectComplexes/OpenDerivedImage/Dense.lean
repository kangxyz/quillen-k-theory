/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.Complements
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Basic


public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.Closure
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.PerfectComplement
public import Quillen.Aglib.CategoryTheory.Abelian.ZeroPushout
public import Quillen.Waldhausen.Cofinality.GeneralDense
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Original dense cofiber data for the derived-saturated open image -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual chosen perfect zero belongs to the original saturated image. -/
theorem zero_mem : objects j (perfectWaldhausen U).zero :=
  of_weakImage j (ApproximationImage.zero_mem (perfectRestrict_waldhausenExact j))

/-- Genuine cofibration pushouts yield original short exact sequences and
hence extension membership in the unchanged chain category. -/
theorem extension_mem (hroof : HasDerivedRoofs j)
    {A B Q : Perfect U} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (perfectWaldhausen U).cof i)
    (h : IsPushout i ((perfectWaldhausen U).isZero.from_ A) q
      ((perfectWaldhausen U).isZero.to_ Q))
    (hA : objects j A) (hQ : objects j Q) : objects j B := by
  have hp := (complexSubcategory_inclusion_exact (locallyPerfect U)).pushout hi h
  have : Mono ((locallyPerfect U).ι.map i) :=
    (complexSubcategory_inclusion_exact (locallyPerfect U)).cofibration i hi
  obtain ⟨z, hz⟩ := Quillen.Abelian.shortExact_of_mono_pushout_zero
    ((locallyPerfect U).ι.map_isZero (perfectWaldhausen U).isZero) hp
  exact complexObjects_of_shortExact j hroof hz hA hQ

/-- The original cofiber is retained in the quotient closure statement. -/
theorem quotient_mem (hroof : HasDerivedRoofs j)
    {A B Q : Perfect U} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (perfectWaldhausen U).cof i)
    (h : IsPushout i ((perfectWaldhausen U).isZero.from_ A) q
      ((perfectWaldhausen U).isZero.to_ Q))
    (hA : objects j A) (hB : objects j B) : objects j Q := by
  have hp := (complexSubcategory_inclusion_exact (locallyPerfect U)).pushout hi h
  have : Mono ((locallyPerfect U).ι.map i) :=
    (complexSubcategory_inclusion_exact (locallyPerfect U)).cofibration i hi
  obtain ⟨z, hz⟩ := Quillen.Abelian.shortExact_of_mono_pushout_zero
    ((locallyPerfect U).ι.map_isZero (perfectWaldhausen U).isZero) hp
  exact complexObjects_quotient_of_shortExact j hroof hz hA hB

/-- All genuine cofinality inputs reduce precisely to the displayed actual
open-derived roof property. Density itself has no further geometric premise. -/
theorem affineDenseData (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (hroof : HasDerivedRoofs W.ι)
    [HasBinaryCoproducts (Perfect W.toScheme)] :
    Cofinality.DenseCofiberData (perfectWaldhausen W.toScheme) (objects W.ι) where
  zero := zero_mem W.ι
  weak f hf := by
    have : QuasiIso f.hom := hf
    exact complexObjects_iff_of_quasiIso W.ι f.hom
  extension := extension_mem W.ι hroof
  quotient := quotient_mem W.ι hroof
  complement := affine_complement R W hW

end Quillen.PerfectComplexes.OpenDerivedImage
