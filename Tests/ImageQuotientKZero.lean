/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.ImageQuotient

/-!
# Consumers of the original image-quotient K-zero equation

These tests retain arbitrary original classes, the actual coarse object loop,
the unchanged change-of-weak-equivalences KMap, and original exact-functor
naturality. They do not assume a coarse presentation or a deficit contraction.
-/
@[expose] public section

noncomputable section
open CategoryTheory Quillen.Waldhausen
open Quillen.Waldhausen.AlgebraicGrothendieck
universe u v
namespace Quillen.Tests.ImageQuotientKZero
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) {V : Structure D} (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (T : FunctorialFactorization V.smallModel)

/-- An arbitrary original K-zero class has exactly its original algebraic quotient value. -/
theorem original_class (x : V.K 0) :
    (imageQuotientGrading W F hF).coarseKZeroValueMap T
      (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0 x) =
    (QuotientAddGroup.mk' (map W F hF).range).toMultiplicative
      ((grothendieckKZeroEquivOfSmallModel V).symm x) :=
  DFunLike.congr_fun (imageQuotientKZeroMap_eq W F hF T) x

/-- The genuine coarse object loop is measured by the literal original quotient map. -/
theorem original_coarse_object (A : D) :
    (imageQuotientGrading W F hF).coarseKZeroValueMap T
      ((imageQuotientGrading W F hF).coarseStructure.kZeroObjectClass A) =
    Multiplicative.ofAdd
      (QuotientAddGroup.mk' (map W F hF).range (objectClass V A)) :=
  imageQuotient_coarseKZeroValueMap_objectClass W F hF T A

/-- The original fine object passes through the actual changeWeak map before evaluation. -/
theorem original_fine_object (A : D) :
    (imageQuotientGrading W F hF).coarseKZeroValueMap T
      (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0
        (V.kZeroObjectClass A)) =
    Multiplicative.ofAdd
      (QuotientAddGroup.mk' (map W F hF).range (objectClass V A)) :=
  imageQuotientKZeroMap_objectClass W F hF T A

/-- The actual coarse group has precisely the original quotient as its value group. -/
theorem original_coarse_bijective :
    Function.Bijective ((imageQuotientGrading W F hF).coarseKZeroValueMap T) :=
  imageQuotient_coarseKZeroValueMap_bijective W F hF T

variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]
  (d : Cofinality.Grading W G) (e : Cofinality.Grading V H)
  (Td : FunctorialFactorization W.smallModel) (φ : G →+ H)
  (hφ : ∀ A, e.value (F.obj A) = φ (d.value A))

include hφ in
/-- Both unchanged changeWeak KMaps commute with the actual exact-functor grading square. -/
theorem original_naturality (x : W.K 0) :
    φ.toMultiplicative (d.coarseKZeroValueMap Td
      (KMap (Fibration.changeWeak_exact d.nested) 0 x)) =
    e.coarseKZeroValueMap T
      (KMap (Fibration.changeWeak_exact e.nested) 0 (KMap hF 0 x)) :=
  DFunLike.congr_fun (d.coarseKZeroValueMap_changeWeak_natural Td e T hF φ hφ) x

end Quillen.Tests.ImageQuotientKZero
