/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Cofinality.CoarseObjectClass
public import Quillen.Waldhausen.Cofinality.GeneralGraded
public import Quillen.Waldhausen.GrothendieckComparison.SmallModel

/-!
# The original coarse K-zero value map in independent universes

This map uses the existing small-model homeomorphism, the proved equality of
coarse structures, and the original coarse grading equivalence. It then forgets
range membership and applies `ULift.down`. Its composite with the unchanged
change-of-weak-equivalences KMap is the original algebraic grading on K-zero.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace Quillen.Waldhausen.Cofinality.Grading
variable {C G : Type u} [Category.{v} C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

private theorem kZeroCast_objectClass {E : Type u} [Category.{v} E]
    {V V' : Structure E} (h : V = V') (A : E) :
    MulEquiv.cast (M := fun S : Structure E ↦ S.K 0) h (V.kZeroObjectClass A) =
      V'.kZeroObjectClass A := by
  cases h
  rfl

/-- The actual original coarse K-zero equivalence with its range-valued small model. -/
def coarseKZeroSmallModelEquiv :
    d.coarseStructure.K 0 ≃* d.smallModelGrading.coarseStructure.K 0 :=
  (d.coarseStructure.smallModelKEquiv 0).trans
    (MulEquiv.cast (M := fun S : Structure (SmallModel C) ↦ S.K 0)
      d.smallModelGrading_coarseStructure.symm)

/-- The explicit transport retains each original coarse object class. -/
@[simp] theorem coarseKZeroSmallModelEquiv_objectClass (A : C) :
    d.coarseKZeroSmallModelEquiv (d.coarseStructure.kZeroObjectClass A) =
      d.smallModelGrading.coarseStructure.kZeroObjectClass (AsSmall.up.obj A) := by
  unfold coarseKZeroSmallModelEquiv
  rw [MulEquiv.trans_apply, Structure.smallModelKEquiv_objectClass]
  exact kZeroCast_objectClass _ _

variable (T : FunctorialFactorization W.smallModel)

/-- The original coarse grading map, with its range inclusion and universe lowering explicit. -/
def coarseKZeroValueMap : d.coarseStructure.K 0 →* Multiplicative G :=
  (((AddEquiv.ulift : ULift.{v} G ≃+ G).toAddMonoidHom.comp
    (d.smallModelGrading.valueRange T).subtype).toMultiplicative).comp
      ((d.smallModelGrading.coarseKZeroEquiv T).toMonoidHom.comp
        d.coarseKZeroSmallModelEquiv.toMonoidHom)

/-- Forgetting range membership and lowering the universe loses no original coarse class. -/
theorem coarseKZeroValueMap_injective : Function.Injective (d.coarseKZeroValueMap T) := by
  have hi : Function.Injective
      (((AddEquiv.ulift : ULift.{v} G ≃+ G).toAddMonoidHom.comp
        (d.smallModelGrading.valueRange T).subtype).toMultiplicative) := by
    intro a b hab
    apply Subtype.ext
    apply ULift.ext
    exact congrArg Multiplicative.toAdd hab
  exact hi.comp ((d.smallModelGrading.coarseKZeroEquiv T).injective.comp
    d.coarseKZeroSmallModelEquiv.injective)

/-- The actual coarse value map returns the unchanged original object grade. -/
@[simp] theorem coarseKZeroValueMap_objectClass (A : C) :
    d.coarseKZeroValueMap T (d.coarseStructure.kZeroObjectClass A) =
      Multiplicative.ofAdd (d.value A) := by
  simp only [coarseKZeroValueMap, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, coarseKZeroSmallModelEquiv_objectClass,
    coarseKZeroEquiv_objectClass]
  rfl

/-- The original change-of-weak-equivalences map followed by the actual coarse grading
is precisely the original algebraic grading under the genuine K-zero comparison. -/
theorem coarseKZeroValueMap_comp_changeWeak :
    (d.coarseKZeroValueMap T).comp (KMap (Fibration.changeWeak_exact d.nested) 0) =
      (AlgebraicGrothendieck.lift W d).toMultiplicative.comp
        (AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel W).symm.toMonoidHom := by
  let e := AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel W
  let f := (d.coarseKZeroValueMap T).comp (KMap (Fibration.changeWeak_exact d.nested) 0)
  let g := (AlgebraicGrothendieck.lift W d).toMultiplicative.comp e.symm.toMonoidHom
  have he : (f.comp e.toMonoidHom).toAdditive = (g.comp e.toMonoidHom).toAdditive := by
    apply AlgebraicGrothendieck.hom_ext W
    intro A
    change f (e (Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass W A))) =
      g (e (Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass W A)))
    change d.coarseKZeroValueMap T
      (KMap (Fibration.changeWeak_exact d.nested) 0
        (AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel W
          (Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass W A)))) =
      (AlgebraicGrothendieck.lift W d).toMultiplicative
        ((AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel W).symm
          (AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel W
            (Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass W A))))
    rw [MulEquiv.symm_apply_apply,
      AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel_objectClass,
      KMap_kZeroObjectClass]
    exact (d.coarseKZeroValueMap_objectClass T A).trans
      (congrArg Multiplicative.ofAdd (AlgebraicGrothendieck.lift_objectClass W d A).symm)
  apply MonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun he a.toAdd

variable {D H : Type u} [Category.{v} D] [AddCommGroup H]
  {V : Structure D} (e : Grading V H) (Te : FunctorialFactorization V.smallModel)
  {F : C ⥤ D} (hF : IsExact W.cof W.weq V.cof V.weq F)
  (φ : G →+ H) (hφ : ∀ A, e.value (F.obj A) = φ (d.value A))

include hφ in
/-- Original exact-functor naturality of the actual fine-to-coarse value composite,
with both original change-of-weak-equivalences KMaps retained. -/
theorem coarseKZeroValueMap_changeWeak_natural :
    φ.toMultiplicative.comp ((d.coarseKZeroValueMap T).comp
      (KMap (Fibration.changeWeak_exact d.nested) 0)) =
    ((e.coarseKZeroValueMap Te).comp
      (KMap (Fibration.changeWeak_exact e.nested) 0)).comp (KMap hF 0) := by
  let c := AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel W
  let f := φ.toMultiplicative.comp ((d.coarseKZeroValueMap T).comp
    (KMap (Fibration.changeWeak_exact d.nested) 0))
  let g := ((e.coarseKZeroValueMap Te).comp
    (KMap (Fibration.changeWeak_exact e.nested) 0)).comp (KMap hF 0)
  have hc : (f.comp c.toMonoidHom).toAdditive = (g.comp c.toMonoidHom).toAdditive := by
    apply AlgebraicGrothendieck.hom_ext W
    intro A
    change f (c (Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass W A))) =
      g (c (Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass W A)))
    change φ.toMultiplicative (d.coarseKZeroValueMap T
      (KMap (Fibration.changeWeak_exact d.nested) 0
        (AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel W
          (Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass W A))))) =
      e.coarseKZeroValueMap Te (KMap (Fibration.changeWeak_exact e.nested) 0
        (KMap hF 0 (AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel W
          (Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass W A)))))
    rw [AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel_objectClass,
      KMap_kZeroObjectClass, KMap_kZeroObjectClass, KMap_kZeroObjectClass]
    exact (congrArg φ.toMultiplicative (d.coarseKZeroValueMap_objectClass T A)).trans
      ((congrArg Multiplicative.ofAdd (hφ A).symm).trans
        (e.coarseKZeroValueMap_objectClass Te (F.obj A)).symm)
  apply MonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := c.surjective x
  exact DFunLike.congr_fun hc a.toAdd

end Quillen.Waldhausen.Cofinality.Grading
