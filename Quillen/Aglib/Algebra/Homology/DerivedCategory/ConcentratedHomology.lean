/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # The original homology single of a concentrated complex -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Cohomological concentration identifies the original complex with the single
on its original homology. No projectivity of that homology is required. -/
def derivedSingleHomologyIso (K : CochainComplex C ℤ) (n : ℤ) [K.IsGE n] [K.IsLE n] :
    DerivedCategory.Q.obj K ≅
      (DerivedCategory.singleFunctor C n).obj (K.homology n) := by
  let h := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Q.obj K) n
  let M := h.choose
  let e := h.choose_spec.some
  let eH : K.homology n ≅ M :=
    ((DerivedCategory.homologyFunctorFactors C n).app K).symm ≪≫
      (DerivedCategory.homologyFunctor C n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app M
  exact e ≪≫ (DerivedCategory.singleFunctor C n).mapIso eH.symm

/-- The comparison identifies the original homology by its actual identity. -/
theorem derivedSingleHomologyIso_homology (K : CochainComplex C ℤ) (n : ℤ)
    [K.IsGE n] [K.IsLE n] :
    ((DerivedCategory.homologyFunctorFactors C n).app K).inv ≫
      (DerivedCategory.homologyFunctor C n).map (derivedSingleHomologyIso K n).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app (K.homology n) = 𝟙 _ := by
  let h := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Q.obj K) n
  let M := h.choose
  let e := h.choose_spec.some
  let eH : K.homology n ≅ M :=
    ((DerivedCategory.homologyFunctorFactors C n).app K).symm ≪≫
      (DerivedCategory.homologyFunctor C n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app M
  change ((DerivedCategory.homologyFunctorFactors C n).app K).inv ≫
    (DerivedCategory.homologyFunctor C n).map
      (e.hom ≫ (DerivedCategory.singleFunctor C n).map eH.inv) ≫ _ = _
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.naturality eH.inv
  change (DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.singleFunctor C n).map eH.inv) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app (K.homology n) =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app M ≫ eH.inv at hn
  rw [hn]
  simpa only [eH, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    HomologicalComplex.homologyFunctor_obj, Functor.id_obj, Category.assoc] using eH.hom_inv_id

end Quillen.CochainComplex
