/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.MappingConeBiprod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The original derived cone of a complementary projector

For arbitrary cochain complexes K and E in an abelian category, the actual
cone of id_K plus zero_E is isomorphic in the original derived category to
the literal complex E plus E shifted by the integer 1. The original cone
inclusion is exactly the projection onto E followed by its inclusion in the
stabilization. This removes the contractible identity block, with no
boundedness or projectivity hypothesis and with an independent derived universe.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe w v u
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
open _root_.CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The genuine derived zero cone is the original complex plus its integer shift. -/
def zeroConeDerivedIso (E : CochainComplex C ℤ) :
    DerivedCategory.Q.obj (mappingCone (0 : E ⟶ E)) ≅ DerivedCategory.Q.obj (E ⊞ E⟦(1 : ℤ)⟧) := by
  let : PreservesBinaryBiproducts (DerivedCategory.Q (C := C)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let T := DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle (0 : E ⟶ E))
  have hT : T ∈ distTriang (DerivedCategory C) := DerivedCategory.mappingCone_triangle_distinguished
    _
  have hz : T.rotate.mor₃ = 0 := by
    dsimp [T, Triangle.rotate]
    simp
  let e := (exists_iso_binaryBiproduct_of_distTriang T.rotate (rot_of_distTriang T hT) hz).choose
  exact e ≪≫ biprod.mapIso (Iso.refl _) ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app E).symm ≪≫
    (DerivedCategory.Q.mapBiprod E (E⟦(1 : ℤ)⟧)).symm

@[reassoc]
lemma zeroConeDerivedIso_inr (E : CochainComplex C ℤ) :
    DerivedCategory.Q.map (mappingCone.inr (0 : E ⟶ E)) ≫ (zeroConeDerivedIso E).hom =
      DerivedCategory.Q.map (biprod.inl : E ⟶ E ⊞ E⟦(1 : ℤ)⟧) := by
  let : PreservesBinaryBiproducts (DerivedCategory.Q (C := C)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let T := DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle (0 : E ⟶ E))
  have hT : T ∈ distTriang (DerivedCategory C) := DerivedCategory.mappingCone_triangle_distinguished
    _
  have hz : T.rotate.mor₃ = 0 := by dsimp [T, Triangle.rotate]; simp
  have he := (exists_iso_binaryBiproduct_of_distTriang T.rotate (rot_of_distTriang T hT)
    hz).choose_spec.1
  change DerivedCategory.Q.map (mappingCone.inr (0 : E ⟶ E)) ≫
      (exists_iso_binaryBiproduct_of_distTriang T.rotate (rot_of_distTriang T hT) hz).choose.hom =
        biprod.inl at he
  dsimp only [zeroConeDerivedIso, Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc, he]
  apply (cancel_mono (DerivedCategory.Q.mapBiprod E (E⟦(1 : ℤ)⟧)).hom).mp
  simp

/-- The actual cone of the complementary projector removes its identity block
and retains exactly the original E and its positive integer shift. -/
def projectorConeDerivedIso (K E : CochainComplex C ℤ) :
    DerivedCategory.Q.obj (mappingCone (biprod.map (𝟙 K) (0 : E ⟶ E))) ≅
      DerivedCategory.Q.obj (E ⊞ E⟦(1 : ℤ)⟧) := by
  let : PreservesBinaryBiproducts (DerivedCategory.Q (C := C)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have hzero : IsZero (DerivedCategory.Q.obj (mappingCone (𝟙 K))) := by
    apply Triangle.isZero₃_of_isIso₁ _ (DerivedCategory.mappingCone_triangle_distinguished (𝟙 K))
    change IsIso (DerivedCategory.Q.map (𝟙 K))
    infer_instance
  exact DerivedCategory.Q.mapIso (mappingConeBiprodIso (𝟙 K) (0 : E ⟶ E)) ≪≫
    DerivedCategory.Q.mapBiprod (mappingCone (𝟙 K)) (mappingCone (0 : E ⟶ E)) ≪≫
    (isoZeroBiprod hzero).symm ≪≫ zeroConeDerivedIso E

@[reassoc]
lemma projectorConeDerivedIso_inr (K E : CochainComplex C ℤ) :
    DerivedCategory.Q.map (mappingCone.inr (biprod.map (𝟙 K) (0 : E ⟶ E))) ≫
      (projectorConeDerivedIso K E).hom =
        DerivedCategory.Q.map ((biprod.snd : K ⊞ E ⟶ E) ≫
          (biprod.inl : E ⟶ E ⊞ E⟦(1 : ℤ)⟧)) := by
  let : PreservesBinaryBiproducts (DerivedCategory.Q (C := C)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  dsimp only [projectorConeDerivedIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    isoZeroBiprod_inv]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
    ← DerivedCategory.Q.map_comp, mappingConeBiprodIso_inr]
  simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd_assoc]
  rw [← Category.assoc, ← DerivedCategory.Q.map_comp, biprod.map_snd, DerivedCategory.Q.map_comp,
    Category.assoc, zeroConeDerivedIso_inr, ← DerivedCategory.Q.map_comp]

end Quillen.CochainComplex
