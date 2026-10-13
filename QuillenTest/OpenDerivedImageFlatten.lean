/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Flatten
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenDerivedImageRoofs

/-!
# Flattening the open derived image

Regression statements compare nested and flattened models, their cofibrations,
and the canonical inclusion maps on K-theory. The affine specializations state
bijectivity in positive degrees and injectivity in degree zero; the general
statements retain the degree-zero range and inverse inclusion equation.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace QuillenTest.OpenDerivedImageFlatten

open Quillen
open PerfectComplexes PerfectComplexes.OpenDerivedImage Waldhausen Fibration
attribute [local instance] Abelian.hasFiniteBiproducts

private def actualCylinder (U : AlgebraicGeometry.Scheme.{u}) :
    RowFactorization.JointData (.refl (perfectWaldhausen U)) :=
  complexJointDataOfNested (locallyPerfect U)
    (fun hK hL f => locallyPerfect_mappingCone hK hL f)
    (fun _ hK => locallyPerfect_shift hK 1) (.refl (perfectWaldhausen U))

private theorem actualCylinder_section (U : AlgebraicGeometry.Scheme.{u}) :
    RowFactorization.SecondEndpointSection (.refl (perfectWaldhausen U)) (actualCylinder U) :=
  complexJointDataOfNested_secondEndpointSection (locallyPerfect U)
    (fun hK hL f => locallyPerfect_mappingCone hK hL f)
    (fun _ hK => locallyPerfect_shift hK 1) (.refl (perfectWaldhausen U))

/-- Actual qc-affine geometry supplies the positive inclusion equivalence, with no roof premise. -/
theorem actual_positive (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (n : ℕ) :
    let : Fact (HasDerivedRoofs W.ι) := ⟨affine_hasDerivedRoofs R W hW⟩
    Function.Bijective (KMap (inclusion_exact W.ι) (n+1)) := by
  let : Fact (HasDerivedRoofs W.ι) := ⟨affine_hasDerivedRoofs R W hW⟩
  let : HasBinaryCoproducts (Perfect W.toScheme) := Additivity.hasBinaryCoproducts
    (perfectWaldhausen _)
  exact inclusion_KMap_succ_bijective W.ι (affineDenseData R W hW (affine_hasDerivedRoofs R W hW))
    (actualCylinder _) (actualCylinder_section _) n

/-- Actual degree zero gives injectivity, without claiming full target surjectivity. -/
theorem actual_zero (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) :
    let : Fact (HasDerivedRoofs W.ι) := ⟨affine_hasDerivedRoofs R W hW⟩
    Function.Injective (KMap (inclusion_exact W.ι) 0) := by
  let : Fact (HasDerivedRoofs W.ι) := ⟨affine_hasDerivedRoofs R W hW⟩
  let : HasBinaryCoproducts (Perfect W.toScheme) := Additivity.hasBinaryCoproducts
    (perfectWaldhausen _)
  exact inclusion_KMap_injective W.ι (affineDenseData R W hW (affine_hasDerivedRoofs R W hW))
    (actualCylinder _) (actualCylinder_section _) 0

/-- The exact original K0 image is independent of the redundant category wrapper. -/
theorem original_zero_range {U X : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Fact (HasDerivedRoofs j)] [HasBinaryCoproducts (Perfect U)]
    (h : Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j)) :
    (KMap (inclusion_exact j) 0).range = (KMap h.inclusion_exact 0).range :=
  flatten_inclusion_range j h 0

/-- A nested original cofibration becomes precisely the same underlying flattened cofibration. -/
theorem original_cofibration {U X : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Fact (HasDerivedRoofs j)] [HasBinaryCoproducts (Perfect U)]
    (h : Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j))
    {A B : Obj j} (f : A ⟶ B) (hf : h.waldhausenStructure.cof f) :
    (complexWaldhausen j).cof ((flatten j).map f) ∧
      ((flatten j).map f).hom = f.hom.hom :=
  ⟨(flatten_exact j h).cofibration f hf, rfl⟩

/-- An original K-class is recovered after inverse flattening and original inclusion. -/
theorem original_inverse_inclusion {U X : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Fact (HasDerivedRoofs j)] [HasBinaryCoproducts (Perfect U)]
    (h : Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j))
    (n : ℕ) (a : (complexWaldhausen j).K n) :
    KMap h.inclusion_exact n ((flattenKEquiv j h n).symm a) = KMap (inclusion_exact j) n a :=
  DFunLike.congr_fun (flattenKEquiv_symm_inclusion j h n) a

end QuillenTest.OpenDerivedImageFlatten
