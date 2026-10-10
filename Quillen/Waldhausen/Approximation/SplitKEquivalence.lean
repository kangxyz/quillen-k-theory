/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Approximation.SplitDeloopingEquivalence
public import Quillen.Topology.HomotopyGroups.Equivalence

/-!
# The canonical change-of-cofibrations K-map is an equivalence

The forward map is the previously defined `splitComplexSubcategoryKMap`,
including its canonical zero-object rebasing. Its bijectivity follows from
the constructed equivalence of the actual S-construction realizations.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CochainComplex

universe v u

namespace Quillen.Waldhausen

section BasedMaps

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- A homotopy equivalence with the prescribed realization map induces a
bijection for any strictly identified image zero object. -/
theorem groupsMapOfZeroEq_bijective_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv W.Delooping V.Delooping)
    (he : e.toFun = (deloopingMap hF).hom)
    (Z : C) (hZ : IsZero Z) (Z' : D) (hZ' : IsZero Z')
    (h : F.obj Z = Z') (n : ℕ) :
    Function.Bijective (groupsMapOfZeroEq hF Z hZ Z' hZ' h n) := by
  subst Z'
  have hp : e.toFun (basepoint W.cof W.weq Z hZ) =
      basepoint V.cof V.weq (F.obj Z) (hF.zero hZ) := by
    rw [he]
    exact deloopingMap_basepoint hF Z hZ
  change Function.Bijective (Quillen.piMap n (deloopingMap hF).hom
    (deloopingMap_basepoint hF Z hZ))
  simpa only [he] using Quillen.piMap_bijective_of_homotopyEquiv e hp n

end BasedMaps

attribute [local instance] Abelian.hasFiniteBiproducts

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- For the canonical identity comparison the rebasing functor is really the
identity: both structures have the same chosen zero and its unique self-iso. -/
theorem splitComparison_rebaseFunctor_eq :
    Quillen.rebaseFunctor (𝟭 P.FullSubcategory)
      (splitComplexSubcategory P).zero (complexSubcategory P).zero
      (((splitComplexSubcategory_to_complexSubcategory_exact P).zero
        (splitComplexSubcategory P).isZero).iso (complexSubcategory P).isZero) =
      𝟭 P.FullSubcategory := by
  have hi : (((splitComplexSubcategory_to_complexSubcategory_exact P).zero
      (splitComplexSubcategory P).isZero).iso (complexSubcategory P).isZero) =
      Iso.refl (complexSubcategory P).zero := by
    apply Iso.ext
    exact (complexSubcategory P).isZero.eq_of_src _ _
  rw [hi]
  exact Quillen.rebaseFunctor_refl _ _

/-- The canonical rebased realization map is the original identity comparison. -/
theorem splitComparison_rebased_deloopingMap :
    deloopingMap (splitComplexSubcategory_to_complexSubcategory_exact P).rebase =
      deloopingMap (splitComplexSubcategory_to_complexSubcategory_exact P) := by
  apply congrArg SSet.toTop.map
  ext n F
  apply Subtype.ext
  exact congrArg (fun G ↦ F.val ⋙ G) (splitComparison_rebaseFunctor_eq P)

variable (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
  ∀ f : K ⟶ L, P (mappingCone f))

include hcone in
/-- Bijectivity of the existing canonical K-map, with no approximation
or equivalence assumption. Cone closure supplies the proved factorization. -/
theorem splitComplexSubcategoryKMap_bijective (n : ℕ) :
    Function.Bijective (splitComplexSubcategoryKMap P n) :=
  groupsMapOfZeroEq_bijective_of_homotopyEquiv
    (splitComplexSubcategory_to_complexSubcategory_exact P).rebase
    (splitDeloopingHomotopyEquiv P hcone)
    ((splitDeloopingHomotopyEquiv_toFun P hcone).trans
      (congrArg TopCat.Hom.hom (splitComparison_rebased_deloopingMap P)).symm)
    (splitComplexSubcategory P).zero (splitComplexSubcategory P).isZero
    (complexSubcategory P).zero (complexSubcategory P).isZero
    (Quillen.rebaseFunctor_obj_base _ _ _ _) n

/-- The actual change-of-cofibrations equivalence of connective K-groups. -/
def splitComplexSubcategoryKEquiv (n : ℕ) :
    (splitComplexSubcategory P).K n ≃* (complexSubcategory P).K n :=
  MulEquiv.ofBijective (splitComplexSubcategoryKMap P n)
    (splitComplexSubcategoryKMap_bijective P hcone n)

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem splitComplexSubcategoryKEquiv_coe (n : ℕ) :
    (↑(splitComplexSubcategoryKEquiv P hcone n) : (splitComplexSubcategory P).K n →*
        (complexSubcategory P).K n) =
      splitComplexSubcategoryKMap P n := rfl


end Quillen.Waldhausen
