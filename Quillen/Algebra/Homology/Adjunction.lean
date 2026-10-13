/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Quillen.Algebra.Homology.KInjectiveHom

/-!
# Genuine complex, homotopy, and injective-target adjunctions

An additive adjunction acts degreewise with its original unit and counit.
Localizing at genuine homotopy equivalences gives the actual homotopy-category
adjunction, with its original quotient-factor squares and literal quotient
unit/counit. At targets where both original target complexes are K-injective,
the actual homotopy-to-derived Hom bijections give an additive derived Hom
equivalence retaining original chain adjoints. No exactness of either functor
is needed for this target-sensitive Hom statement.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Adjunction
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]

/-- The original adjunction acts degreewise, retaining its literal unit and counit. -/
def mapHomologicalComplex {ι : Type w} (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c where
  unit := {
    app K := {
      f n := adj.unit.app (K.X n)
      comm' p q _ := (adj.unit.naturality (K.d p q)).symm }
    naturality {K L} f := by
      ext n : 1
      exact adj.unit.naturality (f.f n) }
  counit := {
    app K := {
      f n := adj.counit.app (K.X n)
      comm' p q _ := (adj.counit.naturality (K.d p q)).symm }
    naturality {K L} f := by
      ext n : 1
      exact adj.counit.naturality (f.f n) }
  left_triangle_components K := by
    ext n : 1
    exact adj.left_triangle_components (K.X n)
  right_triangle_components K := by
    ext n : 1
    exact adj.right_triangle_components (K.X n)

/-- The cochain quotient square for the left adjoint. -/
local instance leftHomotopySquare :
    CatCommSq (F.mapHomologicalComplex (.up ℤ)) (HomotopyCategory.quotient C (.up ℤ))
      (HomotopyCategory.quotient D (.up ℤ)) (F.mapHomotopyCategory (.up ℤ)) :=
  ⟨(F.mapHomotopyCategoryFactors (.up ℤ)).symm⟩

/-- The cochain quotient square for the right adjoint. -/
local instance rightHomotopySquare :
    CatCommSq (G.mapHomologicalComplex (.up ℤ)) (HomotopyCategory.quotient D (.up ℤ))
      (HomotopyCategory.quotient C (.up ℤ)) (G.mapHomotopyCategory (.up ℤ)) :=
  ⟨(G.mapHomotopyCategoryFactors (.up ℤ)).symm⟩

/-- Localization at genuine homotopy equivalences gives the original homotopy-category adjunction.
-/
def mapCochainHomotopyCategory : F.mapHomotopyCategory (.up ℤ) ⊣ G.mapHomotopyCategory (.up ℤ) :=
  (adj.mapHomologicalComplex (.up ℤ)).localization
    (HomotopyCategory.quotient C (.up ℤ)) (HomologicalComplex.homotopyEquivalences C (.up ℤ))
    (HomotopyCategory.quotient D (.up ℤ)) (HomologicalComplex.homotopyEquivalences D (.up ℤ))
    (F.mapHomotopyCategory (.up ℤ)) (G.mapHomotopyCategory (.up ℤ))

/-- The homotopy-category unit is the quotient of the original degreewise unit. -/
lemma mapCochainHomotopyCategory_unit_app (K : CochainComplex C ℤ) :
    adj.mapCochainHomotopyCategory.unit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      (HomotopyCategory.quotient C (.up ℤ)).map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) :=
        by
  rw [mapCochainHomotopyCategory, Adjunction.localization_unit_app]
  change _ ≫ 𝟙 _ ≫ (G.mapHomotopyCategory (.up ℤ)).map (𝟙 _) = _
  simp

/-- The homotopy-category counit is the quotient of the original degreewise counit. -/
lemma mapCochainHomotopyCategory_counit_app (L : CochainComplex D ℤ) :
    adj.mapCochainHomotopyCategory.counit.app ((HomotopyCategory.quotient D (.up ℤ)).obj L) =
      (HomotopyCategory.quotient D (.up ℤ)).map ((adj.mapHomologicalComplex (.up ℤ)).counit.app L)
        := by
  rw [mapCochainHomotopyCategory, Adjunction.localization_counit_app]
  change (F.mapHomotopyCategory (.up ℤ)).map (𝟙 _) ≫ 𝟙 _ ≫ _ = _
  simp

/-- On original complexes the homotopy Hom equivalence has literal quotient endpoints. -/
def cochainHomotopyHomEquiv (K : CochainComplex C ℤ) (L : CochainComplex D ℤ) :
    ((HomotopyCategory.quotient D (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (HomotopyCategory.quotient D (.up ℤ)).obj L) ≃
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj L)) :=
  adj.mapCochainHomotopyCategory.homEquiv _ _

/-- The homotopy adjunction agrees exactly with the original degreewise chain adjunction. -/
@[simp]
lemma cochainHomotopyHomEquiv_map (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    adj.cochainHomotopyHomEquiv K L ((HomotopyCategory.quotient D (.up ℤ)).map f) =
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((adj.mapHomologicalComplex (.up ℤ)).homEquiv K L f) := by
  change adj.mapCochainHomotopyCategory.unit.app _ ≫
    (G.mapHomotopyCategory (.up ℤ)).map ((HomotopyCategory.quotient D (.up ℤ)).map f) = _
  erw [mapCochainHomotopyCategory_unit_app adj K, CategoryTheory.Functor.mapHomotopyCategory_map,
    ← CategoryTheory.Functor.map_comp]
  rfl

end CategoryTheory.Adjunction

universe w'
namespace CategoryTheory.Adjunction
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
  (K : CochainComplex C ℤ) (I : CochainComplex D ℤ)
  [I.IsKInjective] [_root_.CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj I)]

/-- The genuine homotopy adjunction and both injective-target localization bijections give derived
  Hom transport. -/
def cochainDerivedHomEquivOfKInjective :
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶ DerivedCategory.Q.obj I) ≃+
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I)) :=
  ((Quillen.CochainComplex.homotopyDerivedHomEquiv
    ((F.mapHomologicalComplex (.up ℤ)).obj K) I).symm.trans
    (adj.mapCochainHomotopyCategory.homAddEquiv
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)
      ((HomotopyCategory.quotient D (.up ℤ)).obj I))).trans
    (Quillen.CochainComplex.homotopyDerivedHomEquiv K ((G.mapHomologicalComplex (.up ℤ)).obj I))

/-- Actual chain adjoints are preserved by the original derived Hom equivalence. -/
@[simp]
lemma cochainDerivedHomEquivOfKInjective_map
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ I) :
    adj.cochainDerivedHomEquivOfKInjective K I (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv K I f) := by
  change Quillen.CochainComplex.homotopyDerivedHomEquiv K _
    (adj.cochainHomotopyHomEquiv K I
      ((Quillen.CochainComplex.homotopyDerivedHomEquiv _ I).symm (DerivedCategory.Q.map f))) = _
  rw [Quillen.CochainComplex.homotopyDerivedHomEquiv_symm_map,
    cochainHomotopyHomEquiv_map, Quillen.CochainComplex.homotopyDerivedHomEquiv_map]

/-- The inverse equivalence likewise retains the original chain adjoint. -/
@[simp]
lemma cochainDerivedHomEquivOfKInjective_symm_map
    (g : K ⟶ (G.mapHomologicalComplex (.up ℤ)).obj I) :
    (adj.cochainDerivedHomEquivOfKInjective K I).symm (DerivedCategory.Q.map g) =
      DerivedCategory.Q.map (((adj.mapHomologicalComplex (.up ℤ)).homEquiv K I).symm g) := by
  apply (adj.cochainDerivedHomEquivOfKInjective K I).injective
  rw [AddEquiv.apply_symm_apply, cochainDerivedHomEquivOfKInjective_map, Equiv.apply_symm_apply]

end CategoryTheory.Adjunction
