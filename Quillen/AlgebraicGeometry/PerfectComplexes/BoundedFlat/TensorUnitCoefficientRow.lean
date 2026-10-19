/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.TensorZero
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitEdge
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitHomotopy
public import Quillen.Waldhausen.SConstruction.Rows.OneRow
public import Quillen.Waldhausen.SConstruction.Rows.Isomorphism

/-!
# The actual first coefficient tensor row

The coefficient interval diagram is the actual module row `0, O, 0`. Applying the genuine
coefficient tensor functor and evaluating on the second input gives the literal objects
`0 ⊗ K, O ⊗ K, 0 ⊗ K`. Their actual zero isomorphisms identify this whole diagram with the
original one-step quotient row on `O ⊗ K`, before any quotient-row property is transported.
The coefficient row has not yet been identified with its degree-zero Waldhausen K-one class.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows
open scoped Simplicial ZeroObject
universe u
namespace Quillen.PerfectComplexes

/-- The original module coefficient row has the literal objects zero, structure module, zero. -/
def tensorUnitCoefficientRow (X : Scheme.{u}) : Interval ⦋1⦌ ⥤ X.Modules :=
  oneIndex ⋙ ComposableArrows.mk₂
    (0 : (0 : X.Modules) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (0 : SheafOfModules.unit X.ringCatSheaf ⟶ (0 : X.Modules))

/-- Apply genuine tensor to the coefficient row, then evaluate on each independent complex. -/
def complexTensorUnitRows (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ (Interval ⦋1⦌ ⥤ CochainComplex X.Modules ℤ) :=
  (tensorUnitCoefficientRow X ⋙ complexTensorCoefficientFunctor X).flip

/-- The middle coefficient is the original tensor-unit object. -/
theorem complexTensorUnitRows_whole (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    ((complexTensorUnitRows X).obj K).obj (interval 0 1 (by decide)) =
      (tensorLeft (SheafOfModules.unit X.ringCatSheaf)).obj K := rfl

/-- Each original tensor entry remains in the bounded-flat perfect category. -/
theorem complexTensorUnitRows_boundedFlat (X : Scheme.{u}) (K : BoundedFlatPerfect X)
    (p : Interval ⦋1⦌) :
    boundedFlatPerfect X (((complexTensorUnitRows X).obj K.obj).obj p) := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j
  · exact boundedFlatPerfect_of_isZero
      (tensorLeft_isZero_of_coefficient (isZero_zero _) K.obj)
  · exact ((boundedFlatPerfectTensorUnit X).obj K).property
  · exact False.elim (Nat.not_succ_le_zero 0 hij)
  · exact boundedFlatPerfect_of_isZero
      (tensorLeft_isZero_of_coefficient (isZero_zero _) K.obj)

/-- Lift the actual tensor diagrams, without replacing either tensor-zero endpoint. -/
def boundedFlatPerfectTensorUnitRows (X : Scheme.{u}) :
    BoundedFlatPerfect X ⥤ (Interval ⦋1⦌ ⥤ BoundedFlatPerfect X) where
  obj K := (boundedFlatPerfect X).lift ((complexTensorUnitRows X).obj K.obj)
    (complexTensorUnitRows_boundedFlat X K)
  map f :=
    { app p := (boundedFlatPerfect X).homMk (((complexTensorUnitRows X).map f.hom).app p)
      naturality p q g := by
        apply (boundedFlatPerfect X).ι.map_injective
        exact ((complexTensorUnitRows X).map f.hom).naturality g }
  map_id K := by
    apply NatTrans.ext
    funext p
    apply (boundedFlatPerfect X).ι.map_injective
    exact NatTrans.congr_app ((complexTensorUnitRows X).map_id K.obj) p
  map_comp f g := by
    apply NatTrans.ext
    funext p
    apply (boundedFlatPerfect X).ι.map_injective
    exact NatTrans.congr_app ((complexTensorUnitRows X).map_comp f.hom g.hom) p

/-- Both diagonal entries are actual zero objects, as proved from their original tensor terms. -/
theorem boundedFlatPerfectTensorUnitRows_zero (X : Scheme.{u}) (K : BoundedFlatPerfect X)
    (i : Fin 2) :
    IsZero (((boundedFlatPerfectTensorUnitRows X).obj K).obj (interval i i le_rfl)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (boundedFlatPerfect X).ι.map_injective
  fin_cases i <;>
    exact (tensorLeft_isZero_of_coefficient (isZero_zero _) K.obj).eq_of_src _ _

/-- Original tensor-zero isomorphisms and the identity at the actual tensor-unit entry. -/
def tensorUnitRowIsoAt (X : Scheme.{u}) (K : BoundedFlatPerfect X) (p : Interval ⦋1⦌) :
    ((boundedFlatPerfectTensorUnitRows X).obj K).obj p ≅
      (oneDiagram (boundedFlatPerfectWaldhausen X)
        ((boundedFlatPerfectTensorUnit X).obj K)).obj p := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  change Fin 2 at i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      exact (boundedFlatPerfectTensorUnitRows_zero X K 0).iso
        (boundedFlatPerfectWaldhausen X).isZero
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact Iso.refl _
  | succ i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases j using Fin.cases with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hij)
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact (boundedFlatPerfectTensorUnitRows_zero X K 1).iso
        (boundedFlatPerfectWaldhausen X).isZero

/-- All original coefficient arrows commute with the actual endpoint-zero isomorphisms. -/
theorem tensorUnitRowIsoAt_naturality (X : Scheme.{u}) (K : BoundedFlatPerfect X)
    {p q : Interval ⦋1⦌} (f : p ⟶ q) :
    ((boundedFlatPerfectTensorUnitRows X).obj K).map f ≫ (tensorUnitRowIsoAt X K q).hom =
      (tensorUnitRowIsoAt X K p).hom ≫
        (oneDiagram (boundedFlatPerfectWaldhausen X)
          ((boundedFlatPerfectTensorUnit X).obj K)).map f := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  rcases q with ⟨⟨k, l⟩, hkl⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> solve
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact False.elim (Nat.not_succ_le_zero 0 hkl)
  | exact (boundedFlatPerfectTensorUnitRows_zero X K 0).eq_of_src _ _
  | exact (boundedFlatPerfectTensorUnitRows_zero X K 1).eq_of_src _ _
  | exact (boundedFlatPerfectWaldhausen X).isZero.eq_of_tgt _ _
  | have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simp

/-- The entire independently tensored first row is isomorphic to the original one-step row. -/
def tensorUnitRowDiagramIso (X : Scheme.{u}) (K : BoundedFlatPerfect X) :
    (boundedFlatPerfectTensorUnitRows X).obj K ≅
      oneDiagram (boundedFlatPerfectWaldhausen X) ((boundedFlatPerfectTensorUnit X).obj K) :=
  NatIso.ofComponents (tensorUnitRowIsoAt X K) (tensorUnitRowIsoAt_naturality X K)

/-- The actual first tensor row has genuine zero, cofibration and quotient-pushout conditions. -/
theorem boundedFlatPerfectTensorUnitRows_isRow (X : Scheme.{u}) (K : BoundedFlatPerfect X) :
    IsRow (boundedFlatPerfectWaldhausen X) ((boundedFlatPerfectTensorUnitRows X).obj K) :=
  (oneDiagram_isRow (boundedFlatPerfectWaldhausen X) _).of_iso _
    (tensorUnitRowDiagramIso X K).symm

end Quillen.PerfectComplexes
