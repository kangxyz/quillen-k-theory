/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.GradeMap
public import Quillen.Waldhausen.Cofinality.KZeroNaturality
public import Quillen.Waldhausen.GrothendieckGroup.Functor

/-! # Naturality of the original fine Waldhausen K₀ grading map -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
namespace Quillen.Waldhausen.Cofinality.Grading
variable {C D G H : Type u} [SmallCategory C] [SmallCategory D]
  [AddCommGroup G] [AddCommGroup H] {W : Structure C} {V : Structure D}
  (d : Grading W G) (e : Grading V H) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (φ : G →+ H) (hφ : ∀ A, e.value (F.obj A) = φ (d.value A))

include hφ

/-- The fine grading square commutes on the unchanged original grid objects and arrows. -/
theorem fineGradeNerveMap_natural :
    sSetMap hF ≫ e.fineGradeNerveMap =
      d.fineGradeNerveMap ≫ nerveMap φ.toMultiplicative.toFunctor := by
  ext n : 3
  funext X
  refine CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact congrArg Multiplicative.ofAdd (hφ (X.val.obj (0, (⟨(i,j),leOfHom f⟩ : Interval n.unop))))

/-- The square on actual fine homotopy groups uses the original KMap zero rebasing. -/
theorem fineKZeroToGroupPi_natural :
    e.fineKZeroToGroupPi.comp (KMap hF 0) =
      (homotopyGroupMapHom (classifyingSpaceMap φ.toMultiplicative.toFunctor).hom
        (classifyingSpaceMap_point _ (SingleObj.star _))).comp d.fineKZeroToGroupPi := by
  rw [KMap_eq_piMap]
  unfold fineKZeroToGroupPi
  rw [← homotopyGroupMapHom_comp, ← homotopyGroupMapHom_comp]
  congr 1
  change (SSet.toTop.map (sSetMap _) ≫ SSet.toTop.map e.fineGradeNerveMap).hom =
    (SSet.toTop.map d.fineGradeNerveMap ≫ SSet.toTop.map (nerveMap _)).hom
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp]
  congr 2
  exact fineGradeNerveMap_natural d e hF.rebase φ (rebase_value d e hF φ hφ)

/-- The original fine K₀ grading map is natural without any factorization assumption. -/
theorem fineKZeroMap_natural (x : W.K 0) :
    φ.toMultiplicative (d.fineKZeroMap x) = e.fineKZeroMap (KMap hF 0 x) := by
  apply (GroupoidClassifying.singleObjPiOneEquiv _).injective
  rw [← GroupoidClassifying.singleObjPiOneEquiv_natural]
  simp only [fineKZeroMap, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun (fineKZeroToGroupPi_natural d e hF φ hφ) x).symm

end Quillen.Waldhausen.Cofinality.Grading

namespace Quillen.Waldhausen.AlgebraicGrothendieck
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (W : Structure C) (V : Structure D) (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The canonical homotopical-to-classical map respects every original exact functor. -/
theorem kZeroToGrothendieck_natural (x : W.K 0) :
    (map W F hF).toMultiplicative (kZeroToGrothendieck W x) =
      kZeroToGrothendieck V (KMap hF 0 x) :=
  Cofinality.Grading.fineKZeroMap_natural (grading W) (grading V) hF (map W F hF)
    (fun A ↦ (map_objectClass W F hF A).symm) x

end Quillen.Waldhausen.AlgebraicGrothendieck
