/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Quillen.Resolution.Finite

/-!
# Algebraic closure conditions for the resolution theorem

Length-one resolutions upgrade kernel closure to closure under every ambient
admissible subobject. The proof compares two genuine short exact sequences by
their pullback. This is the algebraic reduction used in Weibel V.3.1.1.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)

/-- Closure under the ambient admissible subobjects. Unlike `IsKernelClosed`,
there is no assumption on the quotient object. -/
class IsAdmissibleSubobjectClosed : Prop where
  prop_subobject : ∀ {X Y : C} (i : X ⟶ Y), E.inflation i → P Y → P X

lemma prop_of_inflation [E.IsAdmissibleSubobjectClosed P]
    {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) (hY : P Y) : P X :=
  IsAdmissibleSubobjectClosed.prop_subobject i hi hY

instance kernelClosed_of_admissibleSubobjectClosed [E.IsAdmissibleSubobjectClosed P] :
    E.IsKernelClosed P where
  prop_kernel hS h₂ _ := E.prop_of_inflation P _ (E.inflation_of_conflation hS) h₂

variable [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P] [E.IsKernelClosed P]

/-- If the quotient of an admissible subobject has a length-one resolution,
then kernel and extension closure put the subobject in `P`. -/
lemma prop_kernel_of_quotient_resolution_one {S T : ShortComplex C}
    (hS : E.conflation S) (hT : E.conflation T)
    (hB : P S.X₂) (hT₁ : P T.X₁) (hT₂ : P T.X₂) (e : T.X₃ ≅ S.X₃) :
    P S.X₁ := by
  let T' : ShortComplex C := ShortComplex.mk T.f (T.g ≫ e.hom) (by simp)
  have hT' : E.conflation T' := E.iso_closed (S := T) (T := T')
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp [T']) (by simp [T'])) hT
  let : HasPullback T'.g S.g := E.deflation.hasPullback S.g
    (E.deflation_of_conflation hT')
  let : HasPullback S.g T'.g := hasPullback_symmetry _ _
  have hPB : P (pullback T'.g S.g) := E.prop_pullback P hT' hT₁ hB S.g
  have hPB' : P (pullback S.g T'.g) := P.prop_of_iso (pullbackSymmetry _ _) hPB
  exact IsKernelClosed.prop_kernel (E := E) (P := P)
    (S := pullbackConflation (S := S) T'.X₂ T'.g)
    (E.pullbackConflation_mem hS T'.g) hPB' hT₂

/-- Under length-one resolutions, a resolving full exact subcategory is
closed under all admissible subobjects of its objects. -/
theorem admissibleSubobjectClosed_of_resolutionLength_one
    (h : ∀ X, E.ResolutionLength P 1 X) : E.IsAdmissibleSubobjectClosed P where
  prop_subobject i hi hY := by
    obtain ⟨Z, p, hp, hS⟩ := hi
    obtain ⟨R, hR⟩ := h Z
    cases R with
    | of_mem hZ => exact IsKernelClosed.prop_kernel hS hY hZ
    | step T hT hT₂ R =>
      have hR0 : R.length = 0 := by simpa using hR
      exact E.prop_kernel_of_quotient_resolution_one P hS hT hY
        (R.mem_of_length_eq_zero hR0) hT₂ (Iso.refl _)

end CategoryTheory.ExactCategory.ExactStructure

namespace Quillen.Resolution
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The actual inherited exact inclusion in the resolution theorem. -/
abbrev exactInclusion := ExactSubcategory.exactInclusion E P

/-- The canonical inclusion-induced K-group map. No bijectivity is built into
its type or its data. -/
abbrev inclusionKMap (n : ℕ) := (exactInclusion E P).KMap n

/-- Finite resolutions give algebraic Grothendieck surjectivity without any
homotopical assumption. -/
theorem grothendieckMap_surjective (h : E.ResolutionHypothesis P) :
    Function.Surjective (exactInclusion E P).grothendieckMap := by
  apply AddMonoidHom.range_eq_top.mp
  apply CategoryTheory.ExactCategory.ExactStructure.grothendieckSubgroup_eq_top_of_classes
  intro X
  obtain ⟨R⟩ := h X
  apply R.class_mem
  intro Y hY
  exact ⟨(ExactSubcategory.exactStructure E P).grothendieckClass ⟨Y, hY⟩,
    (exactInclusion E P).grothendieckMap_class ⟨Y, hY⟩⟩

end Quillen.Resolution
