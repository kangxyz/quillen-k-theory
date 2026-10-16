/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Actual chain representatives into a top single

In an abelian category with the original derived category, a derived map from a complex with terms in degrees at most n to a single in degree n has an actual chain representative. The degree bound is retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace Quillen.PerfectComplexes.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
/-- A derived map from a complex supported at most n to a single in degree n
has an actual chain representative. The degree condition is essential; no
projectivity of the source terms is asserted. -/
theorem exists_chain_to_top_single
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE n] (M : C)
    (α : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C n).obj M)) :
    ∃ f : K ⟶ (CochainComplex.singleFunctor C n).obj M, DerivedCategory.Q.map f = α := by
  obtain ⟨L, _, _, g, s, hs, hα⟩ :=
    DerivedCategory.left_fac_of_isStrictlyLE_of_isStrictlyGE n n α
  have : IsIso (DerivedCategory.Q.map s) := hs
  obtain ⟨N, ⟨e⟩⟩ := L.exists_iso_single n
  obtain ⟨φ, hφ⟩ := (CochainComplex.singleFunctor C n).map_surjective (s ≫ e.hom)
  have : IsIso ((DerivedCategory.singleFunctor C n).map φ) := by
    change IsIso (DerivedCategory.Q.map ((CochainComplex.singleFunctor C n).map φ))
    rw [hφ, Functor.map_comp]
    infer_instance
  have : IsIso φ := isIso_of_reflects_iso φ (DerivedCategory.singleFunctor C n)
  have : IsIso (s ≫ e.hom) := by rw [← hφ]; infer_instance
  have : IsIso s := IsIso.of_isIso_comp_right _ e.hom
  refine ⟨g ≫ inv s, ?_⟩
  rw [Functor.map_comp, Functor.map_inv, hα]


end Quillen.PerfectComplexes.ProjectiveLine
end
end
