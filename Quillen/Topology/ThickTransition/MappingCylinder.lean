/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.ThickTransition.Basic
public import Quillen.Topology.MappingCylinder.Fiberwise.RelativeHomotopy
public import Quillen.Topology.HomotopyPullback.StrictComparison

/-!
# Thick interpolation between equivalent fibrations

An ordinary equivalence over the base between genuine fibrations is first
normalized to a fiberwise equivalence. Its actual mapping cylinder has
strong deformations to both ends over that base. Consequently the actual
thickened strip satisfies weak covering-homotopy lifting.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.TheoremB

variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
  (base : C ⟶ T)

/-- The genuine thick mapping-cylinder projection. -/
def thickMappingCylinderProjection :
    C(ThickTransition (TopCat.ι₀ ≫ l).hom c.hom
      ThickTransition.leftConstraint ThickTransition.rightConstraint, T × I) :=
  ThickTransition.projection _ _ _ _ (TheoremA.mappingCylinderProjection sq ≫ base).hom

/-- Explicit fiberwise inverse data on the attaching map imply actual
weak lifting for its thick mapping-cylinder projection. -/
theorem thickMappingCylinder_weakLifting_of_fiberwise_inverse
    (hA : HomotopyLiftingProperty (f ≫ base).hom)
    (hC : HomotopyLiftingProperty base.hom)
    (g : C ⟶ A) (H : TopCat.Homotopy (f ≫ g) (𝟙 A))
    (K : TopCat.Homotopy (g ≫ f) (𝟙 C))
    (hg : g ≫ f ≫ base = base)
    (hH : ∀ t a, base (f (H (t, a))) = base (f a))
    (hK : ∀ t x, base (K (t, x)) = base x) :
    WeakHomotopyLiftingProperty (thickMappingCylinderProjection sq base) := by
  obtain ⟨R₀, hr₀, hR₀⟩ := mappingCylinder_sourceStrongDeformationRetract_over
    sq base g H K hg hH hK
  let R₁ := TheoremA.mappingCylinderTargetStrongDeformationRetract sq
  let D₀ := (TheoremA.homotopyOfCylinder R₀.H R₀.H₀ R₀.H₁).symm
  let D₁ := (mappingCylinderTargetHomotopy sq).symm
  refine ThickTransition.weakLifting (TopCat.ι₀ ≫ l).hom c.hom
    (TheoremA.mappingCylinderProjection sq ≫ base).hom
    (f ≫ base).hom base.hom hA hC ?_ ?_ R₀.r.hom R₁.r.hom ?_ ?_ D₀ D₁ ?_ ?_ ?_ ?_
  · exact congrArg TopCat.Hom.hom (TheoremA.mappingCylinderProjection_start_assoc sq base)
  · exact congrArg TopCat.Hom.hom (TheoremA.mappingCylinderProjection_target_assoc sq base)
  · exact congrArg TopCat.Hom.hom hr₀
  · rfl
  · intro t m
    exact ConcreteCategory.congr_hom hR₀ (m, ULift.up (σ t))
  · intro t m
    exact mappingCylinderTargetHomotopy_over sq base (σ t) m
  · intro t a
    exact ConcreteCategory.congr_hom R₀.fixed (a, ULift.up (σ t))
  · intro t x
    exact ConcreteCategory.congr_hom R₁.fixed (x, ULift.up (σ t))

/-- Ordinary equivalence of the attaching map suffices: all necessary
fiberwise inverse and strong-deformation data are constructed. -/
theorem thickMappingCylinder_weakLifting
    (hA : HomotopyLiftingProperty (f ≫ base).hom)
    (hC : HomotopyLiftingProperty base.hom)
    (e : ContinuousMap.HomotopyEquiv A C) (he : e.toFun = f.hom) :
    WeakHomotopyLiftingProperty (thickMappingCylinderProjection sq base) := by
  let E := fiberwiseEquivOfFibrationHomotopyEquiv (f ≫ base).hom base.hom hA hC e
    (by rw [he]; rfl)
  have hE : E.toMap = f.hom :=
    (fiberwiseEquivOfFibrationHomotopyEquiv_toMap _ _ _ _ _ _).trans he
  let H : TopCat.Homotopy (f ≫ TopCat.ofHom E.invMap) (𝟙 A) :=
    E.left.cast (by rw [hE]; rfl) rfl
  let K : TopCat.Homotopy (TopCat.ofHom E.invMap ≫ f) (𝟙 C) :=
    E.right.cast (by rw [hE]; rfl) rfl
  apply thickMappingCylinder_weakLifting_of_fiberwise_inverse sq base hA hC
    (TopCat.ofHom E.invMap) H K
  · ext x
    exact E.inv_over x
  · exact E.left_over
  · exact E.right_over

end Quillen.TheoremB
