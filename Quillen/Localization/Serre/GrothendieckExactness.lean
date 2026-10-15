/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Localization.Serre.Localization

/-!
# Algebraic Grothendieck-group localization

This file proves exactness for the algebraic group presented by objects and
short exact sequences. It does not identify this group with homotopical K₀.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace Quillen.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The class of an object modulo classes of Serre-class objects. -/
def classModuloSerre (X : C) :
    (abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P :=
  QuotientAddGroup.mk' (serreSubgroup P) ((abelianExactStructure C).grothendieckClass X)

omit [P.IsSerreClass] in
lemma classModuloSerre_eq_zero {X : C} (hX : P X) : classModuloSerre P X = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).2
  exact AddSubgroup.subset_closure ⟨X, hX, rfl⟩

omit [P.IsSerreClass] in
lemma classModuloSerre_additive {S : ShortComplex C} (hS : S.ShortExact) :
    classModuloSerre P S.X₂ = classModuloSerre P S.X₁ + classModuloSerre P S.X₃ := by
  unfold classModuloSerre
  rw [(abelianExactStructure C).grothendieckClass_additive hS, map_add]

lemma classModuloSerre_eq_of_mono {X Y : C} (f : X ⟶ Y) [Mono f]
    (hf : P.epiModSerre f) : classModuloSerre P X = classModuloSerre P Y := by
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f }
  have h := classModuloSerre_additive P hS
  change classModuloSerre P Y = classModuloSerre P X + classModuloSerre P (cokernel f) at h
  rw [classModuloSerre_eq_zero P hf, add_zero] at h
  exact h.symm

lemma classModuloSerre_eq_of_epi {X Y : C} (f : X ⟶ Y) [Epi f]
    (hf : P.monoModSerre f) : classModuloSerre P X = classModuloSerre P Y := by
  have hS : (ShortComplex.mk (kernel.ι f) f (kernel.condition f)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f }
  have h := classModuloSerre_additive P hS
  change classModuloSerre P X = classModuloSerre P (kernel f) + classModuloSerre P Y at h
  rw [classModuloSerre_eq_zero P hf, zero_add] at h
  exact h

/-- An isomorphism modulo the Serre class identifies the two object classes
in the quotient algebraic Grothendieck group. -/
lemma classModuloSerre_eq_of_isoModSerre {X Y : C} (f : X ⟶ Y)
    (hf : P.isoModSerre f) : classModuloSerre P X = classModuloSerre P Y :=
  (classModuloSerre_eq_of_epi P (Abelian.factorThruImage f)
    hf.1.isoModSerre_factorThruImage.1).trans
    (classModuloSerre_eq_of_mono P (Abelian.image.ι f)
      hf.2.isoModSerre_image_ι.2)

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]

/-- Arbitrary isomorphisms in the Serre quotient identify source classes
modulo the Serre subgroup; fractions reduce this to the previous lemma. -/
lemma classModuloSerre_eq_of_localized_iso {X Y : C} (e : L.obj X ≅ L.obj Y) :
    classModuloSerre P X = classModuloSerre P Y := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre e.hom
  have hs := Localization.inverts L P.isoModSerre φ.s φ.hs
  have hcomp : L.map φ.s ≫ e.hom = L.map φ.f := by
    rw [hφ, MorphismProperty.RightFraction.map_s_comp_map]
  have hf : IsIso (L.map φ.f) := by
    rw [← hcomp]
    infer_instance
  exact (classModuloSerre_eq_of_isoModSerre P φ.s φ.hs).symm.trans
    (classModuloSerre_eq_of_isoModSerre P φ.f
      ((ObjectProperty.SerreClassLocalization.isIso_map_iff L P φ.f).1 hf))

/-- The source object class modulo the Serre subgroup, transported to an
object of the quotient using essential surjectivity. -/
def inverseObjClass (Y : D) :
    (abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P :=
  let := Localization.essSurj L P.isoModSerre
  classModuloSerre P (L.objPreimage Y)

lemma inverseObjClass_obj (X : C) :
    inverseObjClass P L (L.obj X) = classModuloSerre P X := by
  let := Localization.essSurj L P.isoModSerre
  exact classModuloSerre_eq_of_localized_iso P L (L.objObjPreimageIso (L.obj X))

lemma inverseObjClass_iso {X Y : D} (e : X ≅ Y) :
    inverseObjClass P L X = inverseObjClass P L Y := by
  let := Localization.essSurj L P.isoModSerre
  exact classModuloSerre_eq_of_localized_iso P L
    (L.objObjPreimageIso X ≪≫ e ≪≫ (L.objObjPreimageIso Y).symm)

/-- The descended object invariant is additive on every quotient short exact
sequence. A lifted monomorphism and its cokernel provide a source sequence. -/
lemma inverseObjClass_additive {S : ShortComplex D} (hS : S.ShortExact) :
    inverseObjClass P L S.X₂ = inverseObjClass P L S.X₁ + inverseObjClass P L S.X₃ := by
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits L P
  obtain ⟨X, Y, f, hf, ⟨e⟩⟩ :=
    (ObjectProperty.SerreClassLocalization.mono_iff L P S.f).1 hS.mono_f
  let : Mono f := hf
  let e₁ : L.obj X ≅ S.X₁ := Arrow.leftFunc.mapIso e
  let e₂ : L.obj Y ≅ S.X₂ := Arrow.rightFunc.mapIso e
  have w : L.map f ≫ e₂.hom = e₁.hom ≫ S.f := e.hom.w.symm
  let e₃ : L.obj (cokernel f) ≅ S.X₃ :=
    PreservesCokernel.iso L f ≪≫ cokernel.mapIso (L.map f) S.f e₁ e₂ w ≪≫
      (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.gIsCokernel
  have hT : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f }
  calc
    inverseObjClass P L S.X₂ = inverseObjClass P L (L.obj Y) :=
      (inverseObjClass_iso P L e₂).symm
    _ = classModuloSerre P Y := inverseObjClass_obj P L Y
    _ = classModuloSerre P X + classModuloSerre P (cokernel f) :=
      classModuloSerre_additive P hT
    _ = inverseObjClass P L (L.obj X) + inverseObjClass P L (L.obj (cokernel f)) := by
      rw [inverseObjClass_obj, inverseObjClass_obj]
    _ = inverseObjClass P L S.X₁ + inverseObjClass P L S.X₃ := by
      rw [inverseObjClass_iso P L e₁, inverseObjClass_iso P L e₃]

/-- The inverse-direction homomorphism from the quotient category's
algebraic Grothendieck group to source classes modulo the Serre subgroup. -/
def inverseGrothendieckMap :
    (abelianExactStructure D).GrothendieckGroup →+
      (abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P :=
  (abelianExactStructure D).grothendieckLift (inverseObjClass P L)
    (fun _ hS => inverseObjClass_additive P L hS)

@[simp]
lemma inverseGrothendieckMap_class (Y : D) :
    inverseGrothendieckMap P L ((abelianExactStructure D).grothendieckClass Y) =
      inverseObjClass P L Y :=
  (abelianExactStructure D).grothendieckLift_class _ _ Y

/-- Returning a localized class to the source gives exactly its class modulo
Serre-class objects. -/
lemma inverseGrothendieckMap_comp :
    (inverseGrothendieckMap P L).comp (grothendieckMap P L) =
      QuotientAddGroup.mk' (serreSubgroup P) := by
  apply (abelianExactStructure C).grothendieck_hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, grothendieckMap_class,
    inverseGrothendieckMap_class, inverseObjClass_obj]
  rfl

lemma inverseGrothendieckMap_leftInverse :
    Function.LeftInverse (inverseGrothendieckMap P L) (grothendieckMapModuloSerre P L) := by
  intro a
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (serreSubgroup P) a
  exact DFunLike.congr_fun (inverseGrothendieckMap_comp P L) x

/-- The descended localization map is injective. Together with surjectivity,
this proves algebraic Grothendieck-group localization. -/
theorem grothendieckMapModuloSerre_injective :
    Function.Injective (grothendieckMapModuloSerre P L) :=
  (inverseGrothendieckMap_leftInverse P L).injective

/-- The kernel of algebraic localization is precisely the subgroup generated
by classes of objects in the Serre class. -/
theorem grothendieckMap_ker : (grothendieckMap P L).ker = serreSubgroup P := by
  apply le_antisymm _ (serreSubgroup_le_ker P L)
  intro a ha
  apply (QuotientAddGroup.eq_zero_iff _).1
  have h := DFunLike.congr_fun (inverseGrothendieckMap_comp P L) a
  change inverseGrothendieckMap P L (grothendieckMap P L a) =
    QuotientAddGroup.mk' (serreSubgroup P) a at h
  rw [show grothendieckMap P L a = 0 from ha, map_zero] at h
  exact h.symm

/-- The algebraic Grothendieck group of the Serre quotient is the source
Grothendieck group modulo classes of Serre-class objects. -/
def grothendieckModuloSerreEquiv :
    ((abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P) ≃+
      (abelianExactStructure D).GrothendieckGroup :=
  AddEquiv.ofBijective (grothendieckMapModuloSerre P L)
    ⟨grothendieckMapModuloSerre_injective P L,
      grothendieckMapModuloSerre_surjective P L⟩

section Canonical

variable {B : Type u₁} [Category.{u₁} B] [Abelian B]
  (P : ObjectProperty B) [P.IsSerreClass]

attribute [local instance] quotientAbelian

/-- Exact kernel statement for the canonical Serre quotient. -/
theorem quotientGrothendieckMap_ker :
    (quotientGrothendieckMap P).ker = serreSubgroup P :=
  grothendieckMap_ker P P.isoModSerre.Q

/-- Algebraic Grothendieck-group localization for the canonical Serre quotient.
This is a statement about the algebraic presentation, not homotopical K₀. -/
def quotientGrothendieckEquiv :
    ((abelianExactStructure B).GrothendieckGroup ⧸ serreSubgroup P) ≃+
      (quotientExactStructure P).GrothendieckGroup :=
  grothendieckModuloSerreEquiv P P.isoModSerre.Q

end Canonical

end Quillen.SerreLocalization
