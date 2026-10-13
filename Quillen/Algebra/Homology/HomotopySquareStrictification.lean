/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.ModuleComplex.ProjectiveStabilization
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Strictifying homotopy triangles with the original identity cone

For an additive functor between arbitrary abelian categories, an actual
homotopy-commuting triangle with a quasi-isomorphic target map becomes strictly
commuting after replacing the original middle object by its sum with an
identity cone. The new target map remains a quasi-isomorphism and agrees with
the original target witness on the literal summand. No exactness or homology
preservation is required of the additive functor.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
universe u₁ v₁ u₂ v₂
namespace Quillen.CochainComplex
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The original identity-cone cylinder middle object. -/
def mapCylinder (A E : CochainComplex C ℤ) : CochainComplex C ℤ :=
  E ⊞ homotopyCofiber (𝟙 A)

/-- The actual source inclusion into the identity-cone cylinder. -/
def mapCylinderInclusion {A E : CochainComplex C ℤ} (a : A ⟶ E) : A ⟶ mapCylinder A E :=
  biprod.lift a (homotopyCofiber.inr (𝟙 A))

/-- An actual homotopy-commuting triangle becomes strictly commuting on the
original identity-cone cylinder. Additivity suffices; no exactness is required. -/
theorem exists_mapCylinder_strictification
    (F : C ⥤ D) [F.Additive]
    {A E : CochainComplex C ℤ} (a : A ⟶ E)
    {B : CochainComplex D ℤ}
    (q : (F.mapHomologicalComplex (.up ℤ)).obj E ⟶ B) [QuasiIso q]
    (f : (F.mapHomologicalComplex (.up ℤ)).obj A ⟶ B)
    (H : Homotopy ((F.mapHomologicalComplex (.up ℤ)).map a ≫ q) f) :
    ∃ p : (F.mapHomologicalComplex (.up ℤ)).obj (mapCylinder A E) ⟶ B,
      QuasiIso p ∧ (F.mapHomologicalComplex (.up ℤ)).map (mapCylinderInclusion a) ≫ p = f ∧
      (F.mapHomologicalComplex (.up ℤ)).map (biprod.inl : E ⟶ mapCylinder A E) ≫ p = q := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  let : PreservesBinaryBiproducts FC := preservesBinaryBiproducts_of_preservesBinaryProducts FC
  let δ : FC.obj A ⟶ B := f - FC.map a ≫ q
  have Hδ : Homotopy (FC.map (𝟙 A) ≫ δ) 0 := by
    simpa [δ, FC] using Homotopy.equivSubZero H.symm
  let c : FC.obj (homotopyCofiber (𝟙 A)) ⟶ B :=
    (homotopyCofiber.mapHomologicalComplexObjIso (𝟙 A) F).hom ≫
      homotopyCofiber.desc (FC.map (𝟙 A)) δ Hδ
  have hc : FC.map (homotopyCofiber.inr (𝟙 A)) ≫ c = δ := by
    dsimp [c, FC]
    simp only [← Category.assoc, homotopyCofiber.inr_mapHomologicalComplexObjIso_hom,
      homotopyCofiber.inr_desc]
  let p : FC.obj (mapCylinder A E) ⟶ B :=
    (FC.mapBiprod E (homotopyCofiber (𝟙 A))).hom ≫ biprod.desc q c
  have hp : FC.map (biprod.inl : E ⟶ mapCylinder A E) ≫ p = q := by
    simp [p, ← Category.assoc, ← FC.map_comp]
  have he : QuasiIso (FC.map (biprod.inl : E ⟶ mapCylinder A E)) :=
    (F.mapHomotopyEquiv (Quillen.ModuleComplex.biprodContractibleHomotopyEquiv E _
      (CochainComplex.mappingCone.homotopyToZeroOfId A))).quasiIso_inv
  have hqp : QuasiIso (FC.map (biprod.inl : E ⟶ mapCylinder A E) ≫ p) := by
    rw [hp]
    infer_instance
  refine ⟨p, (quasiIso_iff_comp_left _ _).mp hqp, ?_, hp⟩
  change FC.map (biprod.lift a (homotopyCofiber.inr (𝟙 A))) ≫
    (FC.mapBiprod E (homotopyCofiber (𝟙 A))).hom ≫ biprod.desc q c = f
  rw [← Category.assoc, biprod.map_lift_mapBiprod, biprod.lift_desc, hc]
  dsimp [δ]
  abel

end Quillen.CochainComplex
