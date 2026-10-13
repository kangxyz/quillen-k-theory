/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Localization.Serre.KernelReflection
public import Quillen.CategoryTheory.TheoremA.ContractibleStructured

/-! # Images of the auxiliary objects as a genuine ordered base -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]

/-- Epi precomposition leaves the image subobject unchanged in an abelian category. -/
lemma imageSubobject_epi_comp {X Y Z : C} (p : X ⟶ Y) [Epi p] (f : Y ⟶ Z) :
    imageSubobject (p ≫ f) = imageSubobject f := by
  let a := Subobject.ofLE _ _ (imageSubobject_comp_le p f)
  have : IsIso a := isIso_of_mono_of_epi a
  exact Subobject.eq_of_comm (asIso a) (Subobject.ofLE_arrow _)

/-- A Q-arrow over the base can only increase the image of its structure map. -/
theorem overQ_image_mono {N : C} {X Y : OverQ N} (f : X ⟶ Y) :
    imageSubobject X.obj.of.hom ≤ imageSubobject Y.obj.of.hom := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  have : Epi s.l.left := s.wl
  rw [← imageSubobject_epi_comp s.l.left X.obj.of.hom, Over.w s.l,
    ← Over.w s.r]
  exact imageSubobject_comp_le s.r.left Y.obj.of.hom

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- The actual image inclusion of a Serre-isomorphism is again a Serre-isomorphism. -/
theorem imageSubobject_arrow_isoModSerre {X N : C} (f : X ⟶ N) (hf : P.isoModSerre f) :
    P.isoModSerre (imageSubobject f).arrow := by
  let L := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits L P
  have : IsIso (L.map f) := Localization.inverts L P.isoModSerre f hf
  have hw : L.map (factorThruImageSubobject f) ≫ L.map (imageSubobject f).arrow = L.map f := by
    rw [← L.map_comp, imageSubobject_arrow_comp]
  have : Epi (L.map (imageSubobject f).arrow) := epi_of_epi_fac hw
  have : IsIso (L.map (imageSubobject f).arrow) := isIso_of_mono_of_epi _
  exact (ObjectProperty.SerreClassLocalization.isIso_map_iff L P _).1 inferInstance

/-- Subobjects of the fixed base whose cokernel belongs to the Serre class. -/
abbrev AuxiliaryImagePoset (N : C) := { I : Subobject N // P.isoModSerre I.arrow }

instance instOrderTopAuxiliaryImagePoset (N : C) : OrderTop (AuxiliaryImagePoset P N) where
  top := ⟨⊤, P.isoModSerre_of_isIso _⟩
  le_top I := show I.val ≤ (⊤ : Subobject N) from le_top

/-- The image index category has a genuine terminal object, the whole base. -/
theorem auxiliaryImagePoset_contractible (N : C) :
    ContractibleSpace (ClassifyingSpace (AuxiliaryImagePoset P N)) :=
  classifyingSpace_contractible_of_isTerminal (isTerminalTop (α := AuxiliaryImagePoset P N))

/-- The image projection is functorial on actual Q-span classes. -/
def auxiliaryImageFunctor (N : C) : AuxiliaryKernel P N ⥤ AuxiliaryImagePoset P N where
  obj X := ⟨imageSubobject X.obj.obj.of.hom,
    imageSubobject_arrow_isoModSerre P _ X.property⟩
  map f := homOfLE (overQ_image_mono f.hom)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The full kernel comma for the entire auxiliary category. -/
abbrev AuxiliaryKernelComma (N : C) (T : (Devissage.subcategoryExactStructure P).QCategory) :=
  CostructuredArrow (auxiliaryKernelFunctor P N) T

/-- The kernel comma has the same concrete image projection. -/
def auxiliaryKernelCommaImageFunctor (N : C)
    (T : (Devissage.subcategoryExactStructure P).QCategory) :
    AuxiliaryKernelComma P N T ⥤ AuxiliaryImagePoset P N :=
  CostructuredArrow.proj _ _ ⋙ auxiliaryImageFunctor P N

/-- Base change to a subobject contained in the image is epimorphic. -/
theorem pullback_to_image_epi {N : C} (X : Over N) (I : Subobject N)
    (hI : I ≤ imageSubobject X.hom) : Epi (pullback.snd X.hom I.arrow) := by
  let t := Subobject.ofLE I (imageSubobject X.hom) hI
  have ht : t ≫ (imageSubobject X.hom).arrow = I.arrow := Subobject.ofLE_arrow _
  have hw : pullback.fst X.hom I.arrow ≫ factorThruImageSubobject X.hom =
      pullback.snd X.hom I.arrow ≫ t := by
    apply (cancel_mono (imageSubobject X.hom).arrow).1
    rw [Category.assoc, imageSubobject_arrow_comp, Category.assoc, ht, pullback.condition]
  have hs : IsPullback (pullback.fst X.hom I.arrow) (pullback.snd X.hom I.arrow)
      (factorThruImageSubobject X.hom) t := by
    apply IsPullback.mk' hw
    · intro Z a b ha hb
      exact pullback.hom_ext ha hb
    · intro Z a b h
      have h' : a ≫ X.hom = b ≫ I.arrow := by
        rw [← imageSubobject_arrow_comp X.hom, ← ht, ← Category.assoc, h, Category.assoc]
      exact ⟨pullback.lift a b h', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  exact MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C) hs inferInstance

end Quillen.SerreLocalization
