/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitAction
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# The original coefficient edge acting by tensor on complexes

Start with the actual module arrow `μr : O ⟶ O`, apply the genuine tensor coefficient functor,
and only then pass to degreewise tensor on complexes. The resulting functor on `[1]` is proved
equal to the edge of the original tensor automorphism. This records the tensor construction
before applying any nerve, Waldhausen normalization or realization.

Intended upstream owner:
`Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitEdge`.
No boundedness hypothesis is needed for the underlying coefficient functor. The current consumer
is the restricted tensor-unit nerve prism in Quillen.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Complex
universe u
namespace Quillen.PerfectComplexes

/-- The actual sheaf coefficient tensor functor applied degreewise to original complexes.
This does not assert exactness for arbitrary coefficient sheaves. -/
def complexTensorCoefficientFunctor (X : Scheme.{u}) :
    X.Modules ⥤ (CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ) where
  obj L := tensorLeft L
  map f := (moduleTensorCoefficientMap X f).mapHomologicalComplex (.up ℤ)
  map_id L := by
    rw [moduleTensorCoefficientMap_id, NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp f g := by
    rw [moduleTensorCoefficientMap_comp, NatTrans.mapHomologicalComplex_comp]

/-- The coefficient edge starts with the original module automorphism, before tensoring. -/
def complexTensorUnitCoefficientEdge (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    Fin 2 ⥤ (CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ) :=
  ComposableArrows.mk₁ (unitMul X r) ⋙ complexTensorCoefficientFunctor X

/-- Tensoring the actual coefficient edge produces the original complex tensor automorphism. -/
theorem complexTensorUnitCoefficientEdge_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    complexTensorUnitCoefficientEdge X r =
      ComposableArrows.mk₁ (complexTensorUnitAutomorphism X r).hom := by
  apply ComposableArrows.ext₁ (F := complexTensorUnitCoefficientEdge X r)
    (G := ComposableArrows.mk₁ (complexTensorUnitAutomorphism X r).hom) rfl rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- Every crossing arrow is the original module coefficient tensor in each complex degree. -/
theorem complexTensorUnitCoefficientEdge_crossing_f (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (((complexTensorUnitCoefficientEdge X r).map (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).app
      K).f n = (moduleTensorCoefficientMap X (unitMul X r)).app (K.X n) := rfl

end Quillen.PerfectComplexes
