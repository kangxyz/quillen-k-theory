/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.FullOpenSectionRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionWaldhausen
public import Quillen.Aglib.CategoryTheory.FiberedCategory.GrothendieckZeroExt

/-!
# The inherited zero under actual full-open section restriction

The original global section-zero family is sent to its specified full-open image-zero
family. The proof retains every actual object and uses the stored equality of base functors
and uniqueness of arrows into the original zero fibers.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

attribute [local irreducible] boundedFlatAffineFullOpenRestrictionStrongTrans
  boundedFlatAffineOriginalEvaluation boundedFlatAffineSectionFullOpenImageZero

/-- The same actual image zero, in precisely the bundled category carried by the fiber. -/
private theorem imageZero_isZero_inFiber (a : Under R) :
    @CategoryTheory.Limits.IsZero ((boundedFlatAffineFullOpenPseudofunctor j).obj ⟨a⟩)
      (Cat.str ((boundedFlatAffineFullOpenPseudofunctor j).obj ⟨a⟩))
      (boundedFlatAffineSectionFullOpenImageZero j a) :=
  isZero_boundedFlatAffineSectionFullOpenImageZero j a

/-- The original restriction sends the original fiber zero to its specified image zero. -/
private theorem imageZero_eq (a : Under R) :
    ((boundedFlatAffineFullOpenRestrictionStrongTrans j).app ⟨a⟩).toFunctor.obj
        (boundedFlatAffineChosenZero a.right) =
      boundedFlatAffineSectionFullOpenImageZero j a := by
  rw [boundedFlatAffineFullOpenRestrictionStrongTrans_app]
  unfold boundedFlatAffineSectionFullOpenImageZero boundedFlatAffineSectionFullOpenRestriction
  simp only [Functor.comp_obj, boundedFlatAffineSectionOpenWaldhausen,
    Waldhausen.Structure.withInverseImageWeak_zero, boundedFlatAffineSectionWaldhausen_zero,
    boundedFlatAffineOriginalEvaluation_sectionZero]
  rfl

/-- Equality of the unchanged original total objects at every section index. -/
theorem boundedFlatAffineFullOpenSectionRestriction_zero_obj
    (a : Under R) (i : Under a) :
    (((boundedFlatAffineFullOpenSectionRestriction j a).obj
        (boundedFlatAffineSectionZero a.right)).obj.val).obj i =
      (boundedFlatAffineFullOpenSectionZero j a).obj.val.obj i := by
  exact congrArg (fun z : (boundedFlatAffineFullOpenPseudofunctor j).obj ⟨i.right⟩ =>
    (⟨i.right, z⟩ : Pseudofunctor.Grothendieck
      (boundedFlatAffineFullOpenPseudofunctor j))) (imageZero_eq j i.right)

/-- The original full-open zero section has zero fibers in their actual bundled categories. -/
private theorem targetFiber_isZero (a : Under R) (i : Under a) :
    Limits.IsZero ((boundedFlatAffineFullOpenSectionZero j a).obj.val.obj i).fiber :=
  imageZero_isZero_inFiber j i.right

attribute [local irreducible] boundedFlatAffineFullOpenSectionRestriction
  boundedFlatAffineSectionZero boundedFlatAffineFullOpenSectionZero

/-- The two original total functors have the same base, using their stored section properties. -/
private theorem zero_base (a : Under R) :
    ((boundedFlatAffineFullOpenSectionRestriction j a).obj
        (boundedFlatAffineSectionZero a.right)).obj.val ⋙
          Pseudofunctor.Grothendieck.forget (boundedFlatAffineFullOpenPseudofunctor j) =
      (boundedFlatAffineFullOpenSectionZero j a).obj.val ⋙
        Pseudofunctor.Grothendieck.forget (boundedFlatAffineFullOpenPseudofunctor j) :=
  (((boundedFlatAffineFullOpenSectionRestriction j a).obj
    (boundedFlatAffineSectionZero a.right)).obj.property).trans
      (boundedFlatAffineFullOpenSectionZero j a).obj.property.symm

/-- The actual restriction and specified target zero have literally equal underlying functors. -/
private theorem zero_functor (a : Under R) :
    ((boundedFlatAffineFullOpenSectionRestriction j a).obj
        (boundedFlatAffineSectionZero a.right)).obj.val =
      (boundedFlatAffineFullOpenSectionZero j a).obj.val := by
  exact Pseudofunctor.Grothendieck.functor_ext_of_base_of_zero
    (S := ((boundedFlatAffineFullOpenSectionRestriction j a).obj
      (boundedFlatAffineSectionZero a.right)).obj.val)
    (T := (boundedFlatAffineFullOpenSectionZero j a).obj.val)
    (boundedFlatAffineFullOpenSectionRestriction_zero_obj j a)
    (zero_base j a)
    (targetFiber_isZero j a)

/-- Original restriction preserves the entire specified image-zero section literally. -/
theorem boundedFlatAffineFullOpenSectionRestriction_sectionZero (a : Under R) :
    (boundedFlatAffineFullOpenSectionRestriction j a).obj
        (boundedFlatAffineSectionZero a.right) =
      boundedFlatAffineFullOpenSectionZero j a := by
  apply ObjectProperty.FullSubcategory.ext
  apply Subtype.ext
  exact zero_functor j a

end Quillen.PerfectComplexes
