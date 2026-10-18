/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.GeometricConeExternalTransport

/-!
# Sixteen original cells of the recursive external-index transport

Both cone/overlap parameter blocks stay fixed. The coefficient is moved by the
literal inverse two-swap word, one actual swap when a factor is empty, and the
original identity when both are empty. All cases refer to the given composite
of the two original inverse index isomorphisms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum Quillen.LoopPrespectrum.StrictSquare
open scoped Topology unitInterval
universe u w
namespace Quillen.KTheory.Bass.GeometricConeInterchange
variable {U : Scheme.{u}} (q : U ⟶ integerBase)
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)

/-- The original external transport preserves the complete target/target parameter blocks. -/
theorem externalTransport_target_target (n : ℕ)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj (laurent.op.obj X)))).space n) :
    ((externalTransport q F).app X).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n (Cell.target (((baseProductFunctor q).op
        ⋙ F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (x))) = Cell.target
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        (Cell.target (F.mapArrow.mapArrow.obj (square (laurent.op.obj ((baseProductFunctor
        q).op.obj X)))) n ((F.map (externalInverse (laurentProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) := by
  exact congrArg (fun k => Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n (Cell.target (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj ((baseProductFunctor q).op.obj X)))) n (k.map n x))) (F.map_comp
        (baseProductSwapMap q (laurentProjection (.of (ULift.{u} ℤ))) (laurent.op.obj
        X).unop).op ((baseProductFunctor (laurentProjection (.of (ULift.{u} ℤ)))).map
        (baseProductSwapMap q (laurentProjection (.of (ULift.{u} ℤ))) X.unop)).op).symm

/-- The original external transport preserves the complete target/upper parameter blocks. -/
theorem externalTransport_target_upper (n : ℕ) (t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (laurent.op.obj X)))).space n) :
    ((externalTransport q F).app X).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n (Cell.upper (((baseProductFunctor q).op
        ⋙ F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (x))) = Cell.target
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        (Cell.upper (F.mapArrow.mapArrow.obj (square (laurent.op.obj ((baseProductFunctor
        q).op.obj X)))) n t ((F.map (externalInverse (laurentProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) := by
  exact congrArg (fun k => Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n (Cell.upper (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj ((baseProductFunctor q).op.obj X)))) n t (k.map n x))) (F.map_comp
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) (laurent.op.obj
        X).unop).op ((baseProductFunctor (polynomialProjection (.of (ULift.{u} ℤ)))).map
        (baseProductSwapMap q (laurentProjection (.of (ULift.{u} ℤ))) X.unop)).op).symm

/-- The original external transport preserves the complete target/lower parameter blocks. -/
theorem externalTransport_target_lower (n : ℕ) (t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (laurent.op.obj X)))).space n) :
    ((externalTransport q F).app X).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n (Cell.lower (((baseProductFunctor q).op
        ⋙ F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (x))) = Cell.target
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        (Cell.lower (F.mapArrow.mapArrow.obj (square (laurent.op.obj ((baseProductFunctor
        q).op.obj X)))) n t ((F.map (externalInverse (laurentProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) := by
  exact congrArg (fun k => Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n (Cell.lower (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj ((baseProductFunctor q).op.obj X)))) n t (k.map n x))) (F.map_comp
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) (laurent.op.obj
        X).unop).op ((baseProductFunctor (polynomialProjection (.of (ULift.{u} ℤ)))).map
        (baseProductSwapMap q (laurentProjection (.of (ULift.{u} ℤ))) X.unop)).op).symm

/-- The original external transport preserves the complete target/overlap parameter blocks. -/
theorem externalTransport_target_overlap (n : ℕ) (t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj X))).space n) :
    ((externalTransport q F).app X).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n (Cell.overlap (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (x))) = Cell.target
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        (Cell.overlap (F.mapArrow.mapArrow.obj (square (laurent.op.obj ((baseProductFunctor
        q).op.obj X)))) n t v ((F.map (baseProductSwapMap q (laurentProjection (.of (ULift.{u}
        ℤ))) X.unop).op).map n x)) := by
  change Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n (Cell.overlap (F.mapArrow.mapArrow.obj (square (laurent.op.obj
        ((baseProductFunctor q).op.obj X)))) n t v ((F.map (baseProductSwapMap q
        (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op).map n ((F.map (𝟙 _)).map n x))) = _
  simp only [F.map_id]
  rfl

/-- The original external transport preserves the complete upper/target parameter blocks. -/
theorem externalTransport_upper_target (n : ℕ) (r : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj (polynomial.op.obj X)))).space n) :
    ((externalTransport q F).app X).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.target (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (x))) = Cell.upper
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        r (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj ((baseProductFunctor
        q).op.obj X)))) n ((F.map (externalInverse (polynomialProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) := by
  exact congrArg (fun k => Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n r (Cell.target (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n (k.map n x))) (F.map_comp
        (baseProductSwapMap q (laurentProjection (.of (ULift.{u} ℤ))) (polynomial.op.obj
        X).unop).op ((baseProductFunctor (laurentProjection (.of (ULift.{u} ℤ)))).map
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) X.unop)).op).symm

/-- The original external transport preserves the complete upper/upper parameter blocks. -/
theorem externalTransport_upper_upper (n : ℕ) (r t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (polynomial.op.obj X)))).space
        n) :
    ((externalTransport q F).app X).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) = Cell.upper
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        r (Cell.upper (F.mapArrow.mapArrow.obj (square (polynomial.op.obj ((baseProductFunctor
        q).op.obj X)))) n t ((F.map (externalInverse (polynomialProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) := by
  exact congrArg (fun k => Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n r (Cell.upper (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n t (k.map n x))) (F.map_comp
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) (polynomial.op.obj
        X).unop).op ((baseProductFunctor (polynomialProjection (.of (ULift.{u} ℤ)))).map
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) X.unop)).op).symm

/-- The original external transport preserves the complete upper/lower parameter blocks. -/
theorem externalTransport_upper_lower (n : ℕ) (r t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (polynomial.op.obj X)))).space
        n) :
    ((externalTransport q F).app X).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) = Cell.upper
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        r (Cell.lower (F.mapArrow.mapArrow.obj (square (polynomial.op.obj ((baseProductFunctor
        q).op.obj X)))) n t ((F.map (externalInverse (polynomialProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) := by
  exact congrArg (fun k => Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n r (Cell.lower (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n t (k.map n x))) (F.map_comp
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) (polynomial.op.obj
        X).unop).op ((baseProductFunctor (polynomialProjection (.of (ULift.{u} ℤ)))).map
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) X.unop)).op).symm

/-- The original external transport preserves the complete upper/overlap parameter blocks. -/
theorem externalTransport_upper_overlap (n : ℕ) (r t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj X))).space n) :
    ((externalTransport q F).app X).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (x))) =
        Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square (polynomial.op.obj
        ((baseProductFunctor q).op.obj X)))) n t v ((F.map (baseProductSwapMap q
        (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).map n x)) := by
  change Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square (polynomial.op.obj
        ((baseProductFunctor q).op.obj X)))) n t v ((F.map (baseProductSwapMap q
        (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).map n ((F.map (𝟙 _)).map n x))) =
        _
  simp only [F.map_id]
  rfl

/-- The original external transport preserves the complete lower/target parameter blocks. -/
theorem externalTransport_lower_target (n : ℕ) (r : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj (polynomial.op.obj X)))).space n) :
    ((externalTransport q F).app X).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.target (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (x))) = Cell.lower
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        r (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj ((baseProductFunctor
        q).op.obj X)))) n ((F.map (externalInverse (polynomialProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) := by
  exact congrArg (fun k => Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n r (Cell.target (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n (k.map n x))) (F.map_comp
        (baseProductSwapMap q (laurentProjection (.of (ULift.{u} ℤ))) (polynomial.op.obj
        X).unop).op ((baseProductFunctor (laurentProjection (.of (ULift.{u} ℤ)))).map
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) X.unop)).op).symm

/-- The original external transport preserves the complete lower/upper parameter blocks. -/
theorem externalTransport_lower_upper (n : ℕ) (r t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (polynomial.op.obj X)))).space
        n) :
    ((externalTransport q F).app X).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) = Cell.lower
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        r (Cell.upper (F.mapArrow.mapArrow.obj (square (polynomial.op.obj ((baseProductFunctor
        q).op.obj X)))) n t ((F.map (externalInverse (polynomialProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) := by
  exact congrArg (fun k => Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n r (Cell.upper (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n t (k.map n x))) (F.map_comp
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) (polynomial.op.obj
        X).unop).op ((baseProductFunctor (polynomialProjection (.of (ULift.{u} ℤ)))).map
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) X.unop)).op).symm

/-- The original external transport preserves the complete lower/lower parameter blocks. -/
theorem externalTransport_lower_lower (n : ℕ) (r t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (polynomial.op.obj X)))).space
        n) :
    ((externalTransport q F).app X).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) = Cell.lower
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        r (Cell.lower (F.mapArrow.mapArrow.obj (square (polynomial.op.obj ((baseProductFunctor
        q).op.obj X)))) n t ((F.map (externalInverse (polynomialProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) := by
  exact congrArg (fun k => Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n r (Cell.lower (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n t (k.map n x))) (F.map_comp
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) (polynomial.op.obj
        X).unop).op ((baseProductFunctor (polynomialProjection (.of (ULift.{u} ℤ)))).map
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) X.unop)).op).symm

/-- The original external transport preserves the complete lower/overlap parameter blocks. -/
theorem externalTransport_lower_overlap (n : ℕ) (r t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj X))).space n) :
    ((externalTransport q F).app X).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (x))) =
        Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square (polynomial.op.obj
        ((baseProductFunctor q).op.obj X)))) n t v ((F.map (baseProductSwapMap q
        (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).map n x)) := by
  change Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square (polynomial.op.obj
        ((baseProductFunctor q).op.obj X)))) n t v ((F.map (baseProductSwapMap q
        (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).map n ((F.map (𝟙 _)).map n x))) =
        _
  simp only [F.map_id]
  rfl

/-- The original external transport preserves the complete overlap/target parameter blocks. -/
theorem externalTransport_overlap_target (n : ℕ) (r s : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj X))).space n) :
    ((externalTransport q F).app X).map n (Cell.overlap ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.target (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square X)) n (x))) = Cell.overlap ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n r s (Cell.target
        (F.mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n ((F.map
        (baseProductSwapMap q (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op).map n x)) :=
        by
  change Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n r s (Cell.target (F.mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n ((F.map (laurent.op.map (𝟙 _))).map n ((F.map (baseProductSwapMap q
        (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op).map n x))) = _
  simp only [laurent.op.map_id, F.map_id]
  rfl

/-- The original external transport preserves the complete overlap/upper parameter blocks. -/
theorem externalTransport_overlap_upper (n : ℕ) (r s t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj X))).space n) :
    ((externalTransport q F).app X).map n (Cell.overlap ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.upper (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square X)) n t (x))) = Cell.overlap ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n r s (Cell.upper
        (F.mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n t ((F.map
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).map n x))
        := by
  change Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n r s (Cell.upper (F.mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n t ((F.map (polynomial.op.map (𝟙 _))).map n ((F.map (baseProductSwapMap
        q (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).map n x))) = _
  simp only [polynomial.op.map_id, F.map_id]
  rfl

/-- The original external transport preserves the complete overlap/lower parameter blocks. -/
theorem externalTransport_overlap_lower (n : ℕ) (r s t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj X))).space n) :
    ((externalTransport q F).app X).map n (Cell.overlap ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.lower (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square X)) n t (x))) = Cell.overlap ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n r s (Cell.lower
        (F.mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n t ((F.map
        (baseProductSwapMap q (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).map n x))
        := by
  change Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n r s (Cell.lower (F.mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n t ((F.map (polynomial.op.map (𝟙 _))).map n ((F.map (baseProductSwapMap
        q (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).map n x))) = _
  simp only [polynomial.op.map_id, F.map_id]
  rfl

/-- The original external transport preserves the complete overlap/overlap parameter blocks. -/
theorem externalTransport_overlap_overlap (n : ℕ) (r s t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj X)).space n) :
    ((externalTransport q F).app X).map n (Cell.overlap ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square X)) n t v (x))) = Cell.overlap
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        r s (Cell.overlap (F.mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        t v (x)) := by
  change Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n r s (Cell.overlap (F.mapArrow.mapArrow.obj (square ((baseProductFunctor
        q).op.obj X))) n t v ((F.map (𝟙 _)).map n ((F.map (𝟙 _)).map n x))) = _
  simp only [F.map_id]
  rfl

end Quillen.KTheory.Bass.GeometricConeInterchange
