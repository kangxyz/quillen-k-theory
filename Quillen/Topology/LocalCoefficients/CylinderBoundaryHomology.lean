/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.CylinderBoundaryChains
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The actual endpoint decomposition on cylinder homology

The two summands are the homology of the original endpoint subspaces with
restricted coefficients. Their maps to cylinder homology are the original
spatial maps, and both are isomorphisms by the explicit cylinder contraction.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits
attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct
open scoped unitInterval
universe u
namespace Quillen.LocalCoefficients
variable (X : Type u) [TopologicalSpace X]

/-- The genuine endpoint corresponding to a Boolean index. -/
def cylinderEndpoint (b : Bool) : unitInterval := if b then 1 else 0

/-- The nested endpoint subspace is homeomorphic to the original space. -/
def cylinderBoundarySliceHomeomorph (b : Bool) :
    cylinderBoundarySlice X (cylinderEndpoint b) ≃ₜ X where
  toFun z := z.val.val.2
  invFun x := ⟨⟨(cylinderEndpoint b, x), by cases b <;> simp [cylinderBoundary,
    cylinderEndpoint]⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext z.property.symm rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The equivalence whose forward map is exactly inclusion of the nested endpoint. -/
def cylinderBoundarySliceInclusionEquiv (b : Bool) :
    ContinuousMap.HomotopyEquiv (cylinderBoundarySlice X (cylinderEndpoint b))
      (unitInterval × X) :=
  (cylinderBoundarySliceHomeomorph X b).toHomotopyEquiv.trans
    (cylinderProjectionEquiv X (cylinderEndpoint b)).symm

/-- The equivalence retains the two original subspace inclusions. -/
theorem cylinderBoundarySliceInclusionEquiv_toFun (b : Bool) :
    (cylinderBoundarySliceInclusionEquiv X b).toFun =
      (subspaceInclusion (cylinderBoundary X)).comp
        (subspaceInclusion (cylinderBoundarySlice X (cylinderEndpoint b))) := by
  apply ContinuousMap.ext
  intro z
  exact Prod.ext z.property.symm rfl

/-- Each actual endpoint summand maps isomorphically to cylinder homology. -/
theorem cylinderBoundarySlice_homology_isIso (b : Bool)
    (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    IsIso (pushforwardHomologyMap
      (subspaceInclusion (cylinderBoundarySlice X (cylinderEndpoint b)))
      (pullback (subspaceInclusion (cylinderBoundary X)) A) n ≫
      pushforwardHomologyMap (subspaceInclusion (cylinderBoundary X)) A n) := by
  have h := isIso_pushforwardHomologyMap_of_homotopyEquiv
    (cylinderBoundarySliceInclusionEquiv X b) A n
  rw [cylinderBoundarySliceInclusionEquiv_toFun] at h
  let e := coefficientHomologyIso
    (pullbackCompositionIso
      (subspaceInclusion (cylinderBoundarySlice X (cylinderEndpoint b)))
      (subspaceInclusion (cylinderBoundary X)) A) n
  have : IsIso (coefficientHomologyMap
      (pullbackCompositionIso
        (subspaceInclusion (cylinderBoundarySlice X (cylinderEndpoint b)))
        (subspaceInclusion (cylinderBoundary X)) A).hom n) := by
    change IsIso e.hom
    infer_instance
  exact IsIso.of_isIso_fac_left
    (pushforwardHomologyMap_comp
      (subspaceInclusion (cylinderBoundarySlice X (cylinderEndpoint b)))
      (subspaceInclusion (cylinderBoundary X)) A n).symm

/-- Actual boundary chains are the direct sum of actual endpoint subspace chains. -/
def cylinderBoundaryChainIso (A : System.{u, u} (cylinderBoundary X)) :
    singularChainComplex (pullback (subspaceInclusion (cylinderBoundarySlice X 0)) A) ⊞
      singularChainComplex (pullback (subspaceInclusion (cylinderBoundarySlice X 1)) A) ≅
    singularChainComplex A :=
  (biprod.mapIso (subspaceSmallChainIso (cylinderBoundarySlice X 0) A)
    (subspaceSmallChainIso (cylinderBoundarySlice X 1) A)).trans
      (cylinderBoundarySmallChainIso X A)

/-- The chain decomposition retains both original endpoint maps. -/
theorem cylinderBoundaryChainIso_hom (A : System.{u, u} (cylinderBoundary X)) :
    (cylinderBoundaryChainIso X A).hom =
      biprod.desc (pushforwardChainMap (subspaceInclusion (cylinderBoundarySlice X 0)) A)
        (pushforwardChainMap (subspaceInclusion (cylinderBoundarySlice X 1)) A) := by
  apply biprod.hom_ext' <;>
    simp [cylinderBoundaryChainIso, cylinderBoundarySmallChainIso_hom]

/-- The actual boundary homology splits into its two endpoint homology summands. -/
def cylinderBoundaryHomologyIso (A : System.{u, u} (cylinderBoundary X)) (n : ℕ) :
    homology (pullback (subspaceInclusion (cylinderBoundarySlice X 0)) A) n ⊞
      homology (pullback (subspaceInclusion (cylinderBoundarySlice X 1)) A) n ≅
    homology A n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n).mapBiprod
      (singularChainComplex (pullback (subspaceInclusion (cylinderBoundarySlice X 0)) A))
      (singularChainComplex (pullback (subspaceInclusion (cylinderBoundarySlice X 1)) A))).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n).mapIso
      (cylinderBoundaryChainIso X A)

/-- Both original spatial homology maps remain the summands of the decomposition. -/
theorem cylinderBoundaryHomologyIso_hom
    (A : System.{u, u} (cylinderBoundary X)) (n : ℕ) :
    (cylinderBoundaryHomologyIso X A n).hom =
      biprod.desc (pushforwardHomologyMap (subspaceInclusion (cylinderBoundarySlice X 0)) A n)
        (pushforwardHomologyMap (subspaceInclusion (cylinderBoundarySlice X 1)) A n) := by
  simp only [cylinderBoundaryHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, cylinderBoundaryChainIso_hom, biprod.mapBiprod_inv_map_desc,
    pushforwardHomologyMap]
  rfl

end Quillen.LocalCoefficients
