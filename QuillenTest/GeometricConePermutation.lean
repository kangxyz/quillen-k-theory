/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.GeometricConeSchemeNaturality
public import Quillen.KTheory.Bass.GeometricConeInvolution

/-!
# Regression for the actual geometric double-cone permutation

The original geometric permutation is an involutive natural isomorphism.
Independent loop time is retained literally; applying the same original map
twice remains identity after looping. The unequal polynomial/Laurent cell
uses the prescribed ordered scheme swap rather than the Laurent self-swap.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen Quillen.LoopPrespectrum Quillen.LoopPrespectrum.StrictSquare
open Quillen.KTheory.Bass.GeometricConeInterchange
open scoped Topology unitInterval
universe u w
namespace QuillenTest.GeometricConePermutation
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)

/-- The unchanged loop parameter remains independent of both cone parameter blocks. -/
theorem original_loop_time (n : ℕ)
    (γ : Path (((coneFunctor.obj (coneFunctor.obj F)).obj X).point n)
      (((coneFunctor.obj (coneFunctor.obj F)).obj X).point n))
    (t : unitInterval) :
    (Path.toContinuousMap ((parameterLoopingMap (permutation F X).hom).map n γ)) t =
      (permutation F X).hom.map n (γ t) := rfl

/-- The actual involution survives the original parameter-looping functor. -/
theorem original_looped_twice :
    parameterLoopingMap (permutation F X).hom ≫ parameterLoopingMap (permutation F X).hom =
      𝟙 (parameterLooping ((coneFunctor.obj (coneFunctor.obj F)).obj X)) := by
  change parameterLoopingFunctor.map (permutation F X).hom ≫
    parameterLoopingFunctor.map (permutation F X).hom = _
  rw [← parameterLoopingFunctor.map_comp, permutation_comp, parameterLoopingFunctor.map_id]
  rfl

/-- The unequal Laurent/polynomial factors keep the exact inverse swap direction. -/
theorem unequal_factors (n : ℕ) (r : unitInterval)
    (x : (F.obj (polynomial.op.obj (laurent.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n
        (Cell.upper (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n r x)) =
      Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r
        (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
          ((F.map (baseProductSwapMap (polynomialProjection (.of (ULift.{u} ℤ)))
            (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op).map n x)) :=
  permutation_target_upper F X n r x

/-- The original functor-level isomorphism has the original component permutation. -/
theorem whole_diagram_component :
    ((permutationFunctorIso.{u,w}).hom.app F).app X = (permutation F X).hom := rfl

#print axioms targetIso
#print axioms permutation
#print axioms permutation_overlap_overlap
#print axioms permutation_comp
#print axioms permutation_inv_eq_hom
#print axioms permutation_diagram_naturality
#print axioms permutation_scheme_naturality
#print axioms permutationFunctorIso
#print axioms original_looped_twice

end QuillenTest.GeometricConePermutation
