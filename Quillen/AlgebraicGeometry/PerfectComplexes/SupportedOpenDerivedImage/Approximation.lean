/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.SupportedOpenDerivedImage.Factorization


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.SupportedOpenDerivedImage.Closure
public import Quillen.Aglib.Algebra.Homology.DerivedCategory.EqualityDenominators
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.HomotopyPullback
public import Quillen.Aglib.Algebra.Homology.HomotopyPullback.QuasiIso
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.Structure
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Fibration
public import Quillen.Waldhausen.WeakArrow.JointData
public import Quillen.Waldhausen.WeakArrow.RelativeKEquivalence
public import Quillen.Waldhausen.Approximation.DualInverseImageLift
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
/-!
# Actual dual approximation with prescribed support

Genuine supported derived roofs supply an actual weak cospan and a common
post-denominator. Two original homotopy pullbacks strictly rectify both
squares. Their component split epimorphisms have actual kernels in the
supported source and image, giving the original dual approximation input.
The relative corestriction comparison uses only genuine opposite joint data;
that structural data is constructed in JointData.
-/
@[expose] public section

open Quillen.CochainComplex
open Quillen.Waldhausen


open AlgebraicGeometry.Scheme.Modules.Complex


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
open Waldhausen
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) [Fact
  (OpenDerivedImage.HasSupportedDerivedRoofs j T)]

/-- Literal opposite weak-arrow model for the original fine restriction. -/
abbrev weakArrowOpposite := WeakArrow.dualWaldhausenStructure
  (perfectSupportedWaldhausen T.ι) (complexWaldhausen j T)
  (perfectSupportedOppositeWaldhausen T.ι) (complexOppositeWaldhausen j T) (complexCorestrict j T)
  (complexCorestrict_exact j T) (complexCorestrict_op_exact j T) (complexOpposite_compatible j T)

/-- Actual incoming lifts on the fine weak-arrow objects. No global fine
reflection is asserted for open restriction. -/
theorem weakArrow_target_lift
    {Z : WeakArrow.Obj (complexWaldhausen j T) (complexCorestrict j T)} {B' : ComplexObj j T}
    (b : B' ⟶ (WeakArrow.target (complexWaldhausen j T) (complexCorestrict j T)).obj Z) :
    ∃ (Y : WeakArrow.Obj (complexWaldhausen j T) (complexCorestrict j T))
      (f : Y ⟶ Z) (v : B' ⟶ (WeakArrow.target (complexWaldhausen j T) (complexCorestrict j T)).obj
        Y),
      (weakArrowOpposite j T).cof.unop f ∧ (complexWaldhausen j T).weq v ∧
      v ≫ (WeakArrow.target (complexWaldhausen j T) (complexCorestrict j T)).map f = b := by
  have hw : QuasiIso Z.obj.hom.hom := Z.property
  obtain ⟨C, D, c, d, u, v, hC, hD, hu, hv, hsq, he, hc, hd, hkc, hkd⟩ :=
    exists_dual_factorization j T (Fact.out : OpenDerivedImage.HasSupportedDerivedRoofs j T)
      Z.obj.left.obj Z.obj.left.property Z.obj.right.obj B'.obj B'.property Z.obj.hom.hom b.hom
  let Y : WeakArrow.Obj (complexWaldhausen j T) (complexCorestrict j T) :=
    ⟨⟨⟨C, hC⟩, ⟨D, hD⟩, ObjectProperty.homMk u⟩, hu⟩
  let f : Y ⟶ Z := ObjectProperty.homMk
    ⟨ObjectProperty.homMk c, ObjectProperty.homMk d, ObjectProperty.hom_ext _ hsq.symm⟩
  have : Epi c := HomologicalComplex.epi_of_epi_f c (fun i => by have := hc i; infer_instance)
  have : Epi d := HomologicalComplex.epi_of_epi_f d (fun i => by have := hd i; infer_instance)
  refine ⟨Y, f, ObjectProperty.homMk v, ?_, hv, ObjectProperty.hom_ext _ he⟩
  constructor
  · apply (ExactSubcategory.deflation_iff (abelianExactStructure (CochainComplex X.Modules ℤ))
      (perfectSupported T.ι)
    f.hom.left).mpr
    refine ⟨kernel c, hkc, kernel.ι c, kernel.condition c, ?_⟩
    exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel c)
            mono_f := inferInstance
            epi_g := by change Epi c; infer_instance }
  · apply (ExactSubcategory.deflation_iff (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j T)
    f.hom.right).mpr
    refine ⟨kernel d, hkd, kernel.ι d, kernel.condition d, ?_⟩
    exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel d)
            mono_f := inferInstance
            epi_g := by change Epi d; infer_instance }

/-- Coarse exactness retains the actual original relative source model. -/
theorem relativeCorestrict_exact : IsExact
    (perfectSupportedOpenWeakWaldhausen j T).cof (perfectSupportedOpenWeakWaldhausen j T).weq
    (complexWaldhausen j T).cof (complexWaldhausen j T).weq (complexCorestrict j T) where
  zero := (complexCorestrict_exact j T).zero
  cofibration := (complexCorestrict_exact j T).cofibration
  weak _ h := h
  pushout := (complexCorestrict_exact j T).pushout

/-- Actual relative restriction is a K-equivalence onto the saturated image,
conditional only on genuine original opposite weak-arrow joint data. -/
theorem relativeCorestrict_KMap_bijective
    (Jd : Fibration.RowFactorization.JointData
      (Fibration.NestedWeakEquivalences.refl (weakArrowOpposite j T))) (n : ℕ) :
    Function.Bijective (KMap (relativeCorestrict_exact j T) n) := by
  let : (complexWaldhausen j T).weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (complexObjects j T)
  apply (WeakArrow.Relative.KMap_bijective_iff_target.{u+1,u}
    (perfectSupportedWaldhausen T.ι) (complexWaldhausen j T) (complexWaldhausen j T)
    (complexCorestrict j T) (𝟭 _) (complexCorestrict_exact j T)
    (IsExact.id (complexWaldhausen j T).cof (complexWaldhausen j T).weq) n).mpr
  exact KMap_bijective_of_dualLift_inverseImage
    (WeakArrow.dual_compatible (perfectSupportedWaldhausen T.ι) (complexWaldhausen j T)
      (perfectSupportedOppositeWaldhausen T.ι) (complexOppositeWaldhausen j T)
      (complexCorestrict j T) (complexCorestrict_exact j T) (complexCorestrict_op_exact j T)
      (complexOpposite_compatible j T) (perfectSupportedOppositeWaldhausen_compatible T.ι))
    (complexOpposite_compatible j T) (complexOpposite_compatible j T)
    (WeakArrow.target_exact (perfectSupportedWaldhausen T.ι) (complexWaldhausen j T)
      (complexCorestrict j T) (complexCorestrict_exact j T))
    (WeakArrow.dual_target_exact (perfectSupportedWaldhausen T.ι) (complexWaldhausen j T)
      (perfectSupportedOppositeWaldhausen T.ι) (complexOppositeWaldhausen j T)
      (complexCorestrict j T) (complexCorestrict_exact j T) (complexCorestrict_op_exact j T)
      (complexOpposite_compatible j T))
    (IsExact.id (complexWaldhausen j T).cof (complexWaldhausen j T).weq)
    (IsExact.id (complexOppositeWaldhausen j T).cof (complexOppositeWaldhausen j T).weq)
    (fun f => weakArrow_target_lift j T f) Jd n

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end
