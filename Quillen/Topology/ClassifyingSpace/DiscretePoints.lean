/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.ClassifyingSpace.Discrete
import Quillen.Topology.HomotopyGroups.ZeroPointClass

/-!
# Actual vertices and components of discrete classifying spaces

The original discrete-realization homeomorphism sends the original vertex to
its object. Those actual vertices biject onto the original zero-dimensional
homotopy classes; no chosen equivalence with unspecified forward map is used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace Quillen

lemma constantRealizationIso_point (A : Type u) (a : A) :
    (TheoremB.constantRealizationIso A).hom
      (realizationPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj A) a) = a := by
  have e : TheoremA.simplicialSigmaι (fun _ : A ↦ (Δ[0] : SSet.{u})) a ≫
      (TheoremA.pointSigmaIso A).hom =
      (SSet.yonedaEquiv (X := (Functor.const SimplexCategoryᵒᵖ).obj A) (n := ⦋0⦌)).symm a := by
    apply SSet.yonedaEquiv.injective
    simp only [Equiv.apply_symm_apply]
    rfl
  have h := ConcreteCategory.congr_hom (TheoremB.constantRealizationIso_ι A a) default
  rw [e] at h
  exact h

lemma discreteClassifyingIso_point (A : Type u) (a : A) :
    (discreteClassifyingIso A).hom (classifyingSpacePoint (Discrete.mk a)) = a := by
  change (TheoremB.constantRealizationIso A).hom
    (SSet.toTop.map (TwoSidedBar.discreteNerveIso A).hom
      (realizationPoint (nerveVertex (Discrete.mk a)))) = _
  rw [realizationPoint_naturality]
  exact constantRealizationIso_point A a

end Quillen

namespace Quillen
lemma discrete_vertex_zeroPointClass_bijective (A : Type u) (a₀ : A) :
    Function.Bijective (fun a : A ↦ zeroPointClass (classifyingSpacePoint (Discrete.mk a₀))
      (classifyingSpacePoint (Discrete.mk a))) := by
  let e := TopCat.homeoOfIso (discreteClassifyingIso A)
  let f := homotopyGroupMap (N := Fin 0) e.toHomotopyEquiv.toFun (discreteClassifyingIso_point A a₀)
  have hf : Function.Bijective f := homotopyGroupMap_bijective_of_homotopyEquiv
    e.toHomotopyEquiv (discreteClassifyingIso_point A a₀) 0
  have he (a : A) : f (zeroPointClass (classifyingSpacePoint (Discrete.mk a₀))
      (classifyingSpacePoint (Discrete.mk a))) = zeroPointClass (X := TopCat.discrete.obj A) a₀ a := by
    change homotopyGroupMap _ _ _ = _
    rw [homotopyGroupMap_zeroPointClass]
    exact congrArg (zeroPointClass (X := TopCat.discrete.obj A) a₀) (discreteClassifyingIso_point A a)
  constructor
  · intro a b h
    apply zeroPointClass_injective_of_discrete (X := TopCat.discrete.obj A) a₀
    exact (he a).symm.trans ((congrArg f h).trans (he b))
  · intro b
    obtain ⟨a, ha⟩ := zeroPointClass_surjective (X := TopCat.discrete.obj A) a₀ (f b)
    exact ⟨a, hf.injective ((he a).trans ha)⟩
end Quillen
