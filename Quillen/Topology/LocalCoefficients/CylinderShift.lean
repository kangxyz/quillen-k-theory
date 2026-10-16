/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.CylinderBoundaryHomology
public import Quillen.Aglib.Algebra.Homology.HomologySequence.ConnectingKernel

/-!
# The relative homology shift for the actual two-ended cylinder

The actual cokernel complex for `(I × X, {0,1} × X)` has homology in degree
`n + 1` isomorphic to cylinder homology in degree `n`. For a system pulled
back from `X`, the original cylinder projection gives the requested shift
to `H_n(X; A)`. The isomorphism uses the original connecting morphism.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped unitInterval
universe u
namespace Quillen.LocalCoefficients
variable (X : Type u) [TopologicalSpace X]

/-- The original endpoint-to-boundary map followed by boundary inclusion. -/
def cylinderEndpointHomologyMap (b : Bool)
    (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    homology (pullback (subspaceInclusion (cylinderBoundarySlice X (cylinderEndpoint b)))
      (pullback (subspaceInclusion (cylinderBoundary X)) A)) n ⟶ homology A n :=
  pushforwardHomologyMap
    (subspaceInclusion (cylinderBoundarySlice X (cylinderEndpoint b)))
    (pullback (subspaceInclusion (cylinderBoundary X)) A) n ≫
    pushforwardHomologyMap (subspaceInclusion (cylinderBoundary X)) A n

/-- Either endpoint induces an isomorphism onto the absolute cylinder homology. -/
instance cylinderEndpointHomologyMap_isIso (b : Bool)
    (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    IsIso (cylinderEndpointHomologyMap X b A n) :=
  cylinderBoundarySlice_homology_isIso X b A n

/-- The endpoint maps identify boundary homology with two copies of cylinder homology. -/
def cylinderBoundaryAdditionIso (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    homology A n ⊞ homology A n ≅
      homology (pullback (subspaceInclusion (cylinderBoundary X)) A) n :=
  biprod.mapIso (asIso (cylinderEndpointHomologyMap X false A n)).symm
    (asIso (cylinderEndpointHomologyMap X true A n)).symm ≪≫
      cylinderBoundaryHomologyIso X (pullback (subspaceInclusion (cylinderBoundary X)) A) n

/-- Under the endpoint identifications, actual boundary inclusion is addition. -/
@[reassoc]
theorem cylinderBoundaryAdditionIso_hom_inclusion
    (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    (cylinderBoundaryAdditionIso X A n).hom ≫
      pushforwardHomologyMap (subspaceInclusion (cylinderBoundary X)) A n =
      biprod.desc (𝟙 (homology A n)) (𝟙 (homology A n)) := by
  apply biprod.hom_ext' <;>
    simp [cylinderBoundaryAdditionIso, cylinderBoundaryHomologyIso_hom,
      cylinderEndpoint] <;> rfl

/-- The original boundary inclusion is epic on homology in every degree. -/
instance cylinderBoundary_homology_epi (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    Epi (pushforwardHomologyMap (subspaceInclusion (cylinderBoundary X)) A n) := by
  have : Epi (pushforwardHomologyMap (subspaceInclusion (cylinderBoundarySlice X 0))
      (pullback (subspaceInclusion (cylinderBoundary X)) A) n ≫
      pushforwardHomologyMap (subspaceInclusion (cylinderBoundary X)) A n) := by
    change Epi (cylinderEndpointHomologyMap X false A n)
    infer_instance
  exact epi_of_epi
    (pushforwardHomologyMap (subspaceInclusion (cylinderBoundarySlice X 0))
      (pullback (subspaceInclusion (cylinderBoundary X)) A) n) _

/-- The actual short complex defining homology relative to the two-ended boundary. -/
def cylinderBoundarySequence (A : System.{u, u} (unitInterval × X)) :
    ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (pushforwardChainMap (subspaceInclusion (cylinderBoundary X)) A)
    (cokernel.π _) (cokernel.condition _)

/-- The original subspace chain inclusion is monic, hence its cokernel sequence is short exact. -/
theorem cylinderBoundarySequence_shortExact (A : System.{u, u} (unitInterval × X)) :
    (cylinderBoundarySequence X A).ShortExact := by
  unfold cylinderBoundarySequence
  exact { exact := ShortComplex.exact_cokernel _ }

/-- The boundary sequence map is epic on the original homology objects. -/
instance cylinderBoundarySequence_homology_epi
    (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    Epi (HomologicalComplex.homologyMap (cylinderBoundarySequence X A).f n) := by
  change Epi (pushforwardHomologyMap (subspaceInclusion (cylinderBoundary X)) A n)
  infer_instance

/-- The original boundary inclusion has the kernel of the addition map. -/
def cylinderBoundaryKernelIso (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    kernel (pushforwardHomologyMap (subspaceInclusion (cylinderBoundary X)) A n) ≅
      kernel (biprod.desc (𝟙 (homology A n)) (𝟙 (homology A n))) :=
  kernel.mapIso _ _ (cylinderBoundaryAdditionIso X A n).symm (Iso.refl _) (by
    apply (cancel_epi (cylinderBoundaryAdditionIso X A n).hom).mp
    simpa only [Iso.refl_hom, Category.comp_id, Category.assoc,
      Iso.symm_hom, Iso.hom_inv_id_assoc] using
      cylinderBoundaryAdditionIso_hom_inclusion X A n)

/-- Relative homology vanishes in degree zero for the actual two-ended cylinder. -/
theorem cylinderRelativeHomology_zero (A : System.{u, u} (unitInterval × X)) :
    IsZero ((relativeSingularChainComplex (cylinderBoundary X) A).homology 0) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact (cylinderBoundarySequence_shortExact X A).exactAt_X₃ 0 inferInstance
    (by intro j hj; simp at hj)

/-- Relative cylinder homology shifts by one, using the actual connecting morphism. -/
def cylinderRelativeHomologyIso (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    (relativeSingularChainComplex (cylinderBoundary X) A).homology (n + 1) ≅
      homology A n :=
  (cylinderBoundarySequence_shortExact X A).connectingKernelIso (n + 1) n rfl ≪≫
    cylinderBoundaryKernelIso X A n ≪≫ kernelAdditionIso (homology A n)

/-- The shift is the original connecting map followed by the first endpoint coordinate. -/
theorem cylinderRelativeHomologyIso_hom
    (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    (cylinderRelativeHomologyIso X A n).hom =
      (cylinderBoundarySequence_shortExact X A).δ (n + 1) n rfl ≫
        (cylinderBoundaryAdditionIso X A n).inv ≫ biprod.fst := by
  simp only [cylinderRelativeHomologyIso, Iso.trans_hom, cylinderBoundaryKernelIso,
    kernel.mapIso_hom, Iso.symm_hom, kernelAdditionIso_hom, Category.assoc, kernel.lift_ι_assoc]
  exact (cylinderBoundarySequence_shortExact X A).connectingKernelIso_hom_ι_assoc
    (n + 1) n rfl _

/-- The original connecting map has the endpoint sign convention `(a, -a)`. -/
@[reassoc]
theorem cylinderRelativeHomologyIso_inv_δ
    (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    (cylinderRelativeHomologyIso X A n).inv ≫
      (cylinderBoundarySequence_shortExact X A).δ (n + 1) n rfl ≫
        (cylinderBoundaryAdditionIso X A n).inv =
      biprod.lift (𝟙 (homology A n)) (-𝟙 (homology A n)) := by
  simp only [cylinderRelativeHomologyIso, Iso.trans_inv, Category.assoc,
    ShortComplex.ShortExact.connectingKernelIso_inv_δ_assoc, cylinderBoundaryKernelIso,
    kernel.mapIso_inv, Iso.symm_inv]
  change (kernelAdditionIso (homology A n)).inv ≫
    kernel.map _ _ (cylinderBoundaryAdditionIso X A n).hom (𝟙 _) _ ≫
      kernel.ι (pushforwardHomologyMap (subspaceInclusion (cylinderBoundary X)) A n) ≫
        (cylinderBoundaryAdditionIso X A n).inv = _
  simp

/-- With pulled-back coefficients, boundary homology is two copies of base homology. -/
def cylinderPullbackBoundaryHomologyIso (A : System.{u, u} X) (n : ℕ) :
    homology A n ⊞ homology A n ≅
      homology (pullback (subspaceInclusion (cylinderBoundary X))
        (pullback (cylinderProjection X) A)) n := by
  have := cylinderProjection_homology_isIso X A n
  exact biprod.mapIso (asIso (pushforwardHomologyMap (cylinderProjection X) A n)).symm
      (asIso (pushforwardHomologyMap (cylinderProjection X) A n)).symm ≪≫
    cylinderBoundaryAdditionIso X (pullback (cylinderProjection X) A) n

/-- Original boundary inclusion and cylinder projection become addition on base homology. -/
@[reassoc]
theorem cylinderPullbackBoundaryHomologyIso_hom_inclusion
    (A : System.{u, u} X) (n : ℕ) :
    (cylinderPullbackBoundaryHomologyIso X A n).hom ≫
      pushforwardHomologyMap (subspaceInclusion (cylinderBoundary X))
        (pullback (cylinderProjection X) A) n ≫
      pushforwardHomologyMap (cylinderProjection X) A n =
      biprod.desc (𝟙 (homology A n)) (𝟙 (homology A n)) := by
  have := cylinderProjection_homology_isIso X A n
  apply biprod.hom_ext' <;>
    simp [cylinderPullbackBoundaryHomologyIso, Category.assoc,
      cylinderBoundaryAdditionIso_hom_inclusion_assoc]

/-- The homology shift for every local system on the original space. -/
def cylinderPullbackRelativeHomologyIso (A : System.{u, u} X) (n : ℕ) :
    (relativeSingularChainComplex (cylinderBoundary X)
      (pullback (cylinderProjection X) A)).homology (n + 1) ≅ homology A n := by
  have := cylinderProjection_homology_isIso X A n
  exact cylinderRelativeHomologyIso X (pullback (cylinderProjection X) A) n ≪≫
    asIso (pushforwardHomologyMap (cylinderProjection X) A n)

/-- The shift to the base uses both the original connecting map and cylinder projection. -/
theorem cylinderPullbackRelativeHomologyIso_hom (A : System.{u, u} X) (n : ℕ) :
    (cylinderPullbackRelativeHomologyIso X A n).hom =
      (cylinderBoundarySequence_shortExact X (pullback (cylinderProjection X) A)).δ
        (n + 1) n rfl ≫
        (cylinderBoundaryAdditionIso X (pullback (cylinderProjection X) A) n).inv ≫
        biprod.fst ≫ pushforwardHomologyMap (cylinderProjection X) A n := by
  simp [cylinderPullbackRelativeHomologyIso, cylinderRelativeHomologyIso_hom,
    Category.assoc]

/-- In base coordinates, the shift is the first component of the original boundary map. -/
theorem cylinderPullbackRelativeHomologyIso_hom_boundary
    (A : System.{u, u} X) (n : ℕ) :
    (cylinderPullbackRelativeHomologyIso X A n).hom =
      (cylinderBoundarySequence_shortExact X (pullback (cylinderProjection X) A)).δ
        (n + 1) n rfl ≫
        (cylinderPullbackBoundaryHomologyIso X A n).inv ≫ biprod.fst := by
  simp [cylinderPullbackRelativeHomologyIso_hom, cylinderPullbackBoundaryHomologyIso,
    Category.assoc]

/-- The original connecting map has sign `(a, -a)` in the two base homology coordinates. -/
@[reassoc]
theorem cylinderPullbackRelativeHomologyIso_inv_δ
    (A : System.{u, u} X) (n : ℕ) :
    (cylinderPullbackRelativeHomologyIso X A n).inv ≫
      (cylinderBoundarySequence_shortExact X (pullback (cylinderProjection X) A)).δ
        (n + 1) n rfl ≫ (cylinderPullbackBoundaryHomologyIso X A n).inv =
      biprod.lift (𝟙 (homology A n)) (-𝟙 (homology A n)) := by
  have := cylinderProjection_homology_isIso X A n
  simp only [cylinderPullbackRelativeHomologyIso, cylinderPullbackBoundaryHomologyIso,
    Iso.trans_inv, biprod.mapIso_inv, Iso.symm_inv, asIso_hom, Category.assoc,
    cylinderRelativeHomologyIso_inv_δ_assoc]
  apply biprod.hom_ext <;> simp [Category.assoc]

end Quillen.LocalCoefficients
