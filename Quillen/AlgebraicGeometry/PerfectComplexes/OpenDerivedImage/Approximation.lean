/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Structure
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.DualFactorization
public import Quillen.Waldhausen.WeakArrow.JointData
public import Quillen.Waldhausen.WeakArrow.RelativeKEquivalence
public import Quillen.Waldhausen.Approximation.DualInverseImageLift

/-! # Original relative restriction onto the saturated target

Fine weak-arrow objects and stored quasi-isomorphisms are unchanged. Coarse
reflection follows by definition, while actual incoming factorization is
constructed from geometric roofs. Genuine joint data remains an explicit
structural input until the cross-category cocylinder comparison is supplied.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [Fact (HasDerivedRoofs j)]

/-- Literal opposite weak-arrow model for the original fine restriction. -/
abbrev weakArrowOpposite := WeakArrow.dualWaldhausenStructure
  (perfectWaldhausen X) (complexWaldhausen j)
  (perfectOppositeWaldhausen X) (complexOppositeWaldhausen j) (complexCorestrict j)
  (complexCorestrict_exact j) (complexCorestrict_op_exact j) (complexOpposite_compatible j)

/-- Actual incoming lifts on the fine weak-arrow objects. No global fine
reflection is asserted for open restriction. -/
theorem weakArrow_target_lift
    {Z : WeakArrow.Obj (complexWaldhausen j) (complexCorestrict j)} {B' : ComplexObj j}
    (b : B' ⟶ (WeakArrow.target (complexWaldhausen j) (complexCorestrict j)).obj Z) :
    ∃ (Y : WeakArrow.Obj (complexWaldhausen j) (complexCorestrict j))
      (f : Y ⟶ Z) (v : B' ⟶ (WeakArrow.target (complexWaldhausen j) (complexCorestrict j)).obj Y),
      (weakArrowOpposite j).cof.unop f ∧ (complexWaldhausen j).weq v ∧
      v ≫ (WeakArrow.target (complexWaldhausen j) (complexCorestrict j)).map f = b := by
  have hw : QuasiIso Z.obj.hom.hom := Z.property
  obtain ⟨C, D, c, d, u, v, hC, hD, hu, hv, hsq, he, hc, hd, hkc, hkd⟩ :=
    exists_dual_factorization j (Fact.out : HasDerivedRoofs j)
      Z.obj.left.obj Z.obj.left.property Z.obj.right.obj B'.obj B'.property Z.obj.hom.hom b.hom
  let Y : WeakArrow.Obj (complexWaldhausen j) (complexCorestrict j) :=
    ⟨⟨⟨C, hC⟩, ⟨D, hD⟩, ObjectProperty.homMk u⟩, hu⟩
  let f : Y ⟶ Z := ObjectProperty.homMk
    ⟨ObjectProperty.homMk c, ObjectProperty.homMk d, ObjectProperty.hom_ext _ hsq.symm⟩
  have : Epi c := HomologicalComplex.epi_of_epi_f c (fun i => by have := hc i; infer_instance)
  have : Epi d := HomologicalComplex.epi_of_epi_f d (fun i => by have := hd i; infer_instance)
  refine ⟨Y, f, ObjectProperty.homMk v, ?_, hv, ObjectProperty.hom_ext _ he⟩
  constructor
  · apply (ExactSubcategory.deflation_iff (abelianExactStructure (Complex X)) (locallyPerfect X)
    f.hom.left).mpr
    refine ⟨kernel c, hkc, kernel.ι c, kernel.condition c, ?_⟩
    exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel c)
            mono_f := inferInstance
            epi_g := by change Epi c; infer_instance }
  · apply (ExactSubcategory.deflation_iff (abelianExactStructure (Complex U)) (complexObjects j)
    f.hom.right).mpr
    refine ⟨kernel d, hkd, kernel.ι d, kernel.condition d, ?_⟩
    exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel d)
            mono_f := inferInstance
            epi_g := by change Epi d; infer_instance }

/-- Coarse exactness retains the actual original relative source model. -/
theorem relativeCorestrict_exact : IsExact
    (perfectOpenWeakWaldhausen j).cof (perfectOpenWeakWaldhausen j).weq
    (complexWaldhausen j).cof (complexWaldhausen j).weq (complexCorestrict j) where
  zero := (complexCorestrict_exact j).zero
  cofibration := (complexCorestrict_exact j).cofibration
  weak _ h := h
  pushout := (complexCorestrict_exact j).pushout

/-- Actual relative restriction is a K-equivalence onto the saturated image,
conditional only on genuine original opposite weak-arrow joint data. -/
theorem relativeCorestrict_KMap_bijective
    (Jd : Fibration.RowFactorization.JointData
      (Fibration.NestedWeakEquivalences.refl (weakArrowOpposite j))) (n : ℕ) :
    Function.Bijective (KMap (relativeCorestrict_exact j) n) := by
  let : (complexWaldhausen j).weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (complexObjects j)
  apply (WeakArrow.Relative.KMap_bijective_iff_target.{u+1,u}
    (perfectWaldhausen X) (complexWaldhausen j) (complexWaldhausen j)
    (complexCorestrict j) (𝟭 _) (complexCorestrict_exact j)
    (IsExact.id (complexWaldhausen j).cof (complexWaldhausen j).weq) n).mpr
  exact KMap_bijective_of_dualLift_inverseImage
    (WeakArrow.dual_compatible (perfectWaldhausen X) (complexWaldhausen j)
      (perfectOppositeWaldhausen X) (complexOppositeWaldhausen j)
      (complexCorestrict j) (complexCorestrict_exact j) (complexCorestrict_op_exact j)
      (complexOpposite_compatible j) (perfectOppositeWaldhausen_compatible X))
    (complexOpposite_compatible j) (complexOpposite_compatible j)
    (WeakArrow.target_exact (perfectWaldhausen X) (complexWaldhausen j)
      (complexCorestrict j) (complexCorestrict_exact j))
    (WeakArrow.dual_target_exact (perfectWaldhausen X) (complexWaldhausen j)
      (perfectOppositeWaldhausen X) (complexOppositeWaldhausen j)
      (complexCorestrict j) (complexCorestrict_exact j) (complexCorestrict_op_exact j)
      (complexOpposite_compatible j))
    (IsExact.id (complexWaldhausen j).cof (complexWaldhausen j).weq)
    (IsExact.id (complexOppositeWaldhausen j).cof (complexOppositeWaldhausen j).weq)
    (fun f => weakArrow_target_lift j f) Jd n

end Quillen.PerfectComplexes.OpenDerivedImage
