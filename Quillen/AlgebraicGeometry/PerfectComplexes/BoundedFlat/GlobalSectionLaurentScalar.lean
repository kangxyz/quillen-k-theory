/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionRestrictionUnit

/-! # Explicit original scalar equality for the global Laurent action -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- A specified scalar equality specializes the unchanged global reindex action law. -/
theorem globalUnit_reindex_of_eq {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y)
    (r : (Γ(X.unop, ⊤))ˣ) (s : (Γ(Y.unop, ⊤))ˣ)
    (h : Units.map f.unop.appTop.hom.toMonoidHom r = s) :
    Preserves (globalModel.map f).functor (globalUnit X r) (globalUnit Y s) := by
  subst s
  exact globalUnit_reindex f r

/-- The actual coefficient projection pulls the forward Laurent coordinate back literally. -/
theorem globalLaurentScalar_map {R : CommRingCat.{u}} (P : Over (Spec R))
    {a b : Under R} (g : a ⟶ b) :
    Units.map (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (show (op P, (laurentUnderFunctor R).obj a) ⟶
          (op P, (laurentUnderFunctor R).obj b) from
        (𝟙 (op P), (laurentUnderFunctor R).map g))).appTop.hom.toMonoidHom
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
        (laurentGlobalUnit a.right)) =
      boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
        (laurentGlobalUnit b.right) := by
  rw [boundedFlatCoefficientUnit_map]
  have hr : Units.map (Spec.map ((laurentUnderFunctor R).map g).right).appTop.hom.toMonoidHom
      (laurentGlobalUnit a.right) = laurentGlobalUnit b.right :=
    laurentGlobalUnit_coefficient g.right
  exact congrArg (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)) hr

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
