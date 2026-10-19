/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientRow
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportHomotopy

/-!
# The actual first coefficient tensor row inside supported complexes

Every entry is the original coefficient tensor complex, proved acyclic on the given open.
The row predicates are established inside the original supported Waldhausen category by
its actual tensor-zero isomorphisms and supported one-step row.
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
variable {U X : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]

/-- Each original tensor entry remains in the bounded-flat perfect category. -/
theorem complexTensorUnitRows_supported (K : (boundedFlatPerfectSupported ι).FullSubcategory)
    (p : Interval ⦋1⦌) :
    boundedFlatPerfectSupported ι (((complexTensorUnitRows X).obj K.obj).obj p) := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j
  · exact ⟨boundedFlatPerfect_of_isZero
      (tensorLeft_isZero_of_coefficient (isZero_zero _) K.obj),
      HomologicalComplex.acyclic_of_isZero _ ((restrict ι).map_isZero
        (tensorLeft_isZero_of_coefficient (isZero_zero _) K.obj))⟩
  · exact ((boundedFlatPerfectSupportedTensorUnit ι).obj K).property
  · exact False.elim (Nat.not_succ_le_zero 0 hij)
  · exact ⟨boundedFlatPerfect_of_isZero
      (tensorLeft_isZero_of_coefficient (isZero_zero _) K.obj),
      HomologicalComplex.acyclic_of_isZero _ ((restrict ι).map_isZero
        (tensorLeft_isZero_of_coefficient (isZero_zero _) K.obj))⟩

/-- Lift the actual tensor diagrams, without replacing either tensor-zero endpoint. -/
def boundedFlatPerfectSupportedTensorUnitRows :
    (boundedFlatPerfectSupported ι).FullSubcategory ⥤
      (Interval ⦋1⦌ ⥤ (boundedFlatPerfectSupported ι).FullSubcategory) where
  obj K := (boundedFlatPerfectSupported ι).lift ((complexTensorUnitRows X).obj K.obj)
    (complexTensorUnitRows_supported ι K)
  map f :=
    { app p := (boundedFlatPerfectSupported ι).homMk (((complexTensorUnitRows X).map f.hom).app p)
      naturality p q g := by
        apply (boundedFlatPerfectSupported ι).ι.map_injective
        exact ((complexTensorUnitRows X).map f.hom).naturality g }
  map_id K := by
    apply NatTrans.ext
    funext p
    apply (boundedFlatPerfectSupported ι).ι.map_injective
    exact NatTrans.congr_app ((complexTensorUnitRows X).map_id K.obj) p
  map_comp f g := by
    apply NatTrans.ext
    funext p
    apply (boundedFlatPerfectSupported ι).ι.map_injective
    exact NatTrans.congr_app ((complexTensorUnitRows X).map_comp f.hom g.hom) p

/-- Both diagonal entries are actual zero objects, as proved from their original tensor terms. -/
theorem boundedFlatPerfectSupportedTensorUnitRows_zero
    (K : (boundedFlatPerfectSupported ι).FullSubcategory)
    (i : Fin 2) :
    IsZero (((boundedFlatPerfectSupportedTensorUnitRows ι).obj K).obj (interval i i le_rfl)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (boundedFlatPerfectSupported ι).ι.map_injective
  fin_cases i <;>
    exact (tensorLeft_isZero_of_coefficient (isZero_zero _) K.obj).eq_of_src _ _

/-- Original tensor-zero isomorphisms and the identity at the actual tensor-unit entry. -/
def supportedTensorUnitRowIsoAt (K : (boundedFlatPerfectSupported ι).FullSubcategory)
    (p : Interval ⦋1⦌) :
    ((boundedFlatPerfectSupportedTensorUnitRows ι).obj K).obj p ≅
      (oneDiagram (boundedFlatPerfectSupportedWaldhausen ι)
        ((boundedFlatPerfectSupportedTensorUnit ι).obj K)).obj p := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  change Fin 2 at i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      exact (boundedFlatPerfectSupportedTensorUnitRows_zero ι K 0).iso
        (boundedFlatPerfectSupportedWaldhausen ι).isZero
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
      exact (boundedFlatPerfectSupportedTensorUnitRows_zero ι K 1).iso
        (boundedFlatPerfectSupportedWaldhausen ι).isZero

/-- All original coefficient arrows commute with the actual endpoint-zero isomorphisms. -/
theorem supportedTensorUnitRowIsoAt_naturality
    (K : (boundedFlatPerfectSupported ι).FullSubcategory)
    {p q : Interval ⦋1⦌} (f : p ⟶ q) :
    ((boundedFlatPerfectSupportedTensorUnitRows ι).obj K).map f ≫
        (supportedTensorUnitRowIsoAt ι K q).hom =
      (supportedTensorUnitRowIsoAt ι K p).hom ≫
        (oneDiagram (boundedFlatPerfectSupportedWaldhausen ι)
          ((boundedFlatPerfectSupportedTensorUnit ι).obj K)).map f := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  rcases q with ⟨⟨k, l⟩, hkl⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> solve
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact False.elim (Nat.not_succ_le_zero 0 hkl)
  | exact (boundedFlatPerfectSupportedTensorUnitRows_zero ι K 0).eq_of_src _ _
  | exact (boundedFlatPerfectSupportedTensorUnitRows_zero ι K 1).eq_of_src _ _
  | exact (boundedFlatPerfectSupportedWaldhausen ι).isZero.eq_of_tgt _ _
  | have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simp

/-- The entire independently tensored first row is isomorphic to the original one-step row. -/
def supportedTensorUnitRowDiagramIso (K : (boundedFlatPerfectSupported ι).FullSubcategory) :
    (boundedFlatPerfectSupportedTensorUnitRows ι).obj K ≅
      oneDiagram (boundedFlatPerfectSupportedWaldhausen ι)
        ((boundedFlatPerfectSupportedTensorUnit ι).obj K) :=
  NatIso.ofComponents (supportedTensorUnitRowIsoAt ι K) (supportedTensorUnitRowIsoAt_naturality ι K)

/-- The actual first tensor row has genuine zero, cofibration and quotient-pushout conditions. -/
theorem boundedFlatPerfectSupportedTensorUnitRows_isRow
    (K : (boundedFlatPerfectSupported ι).FullSubcategory) :
    IsRow (boundedFlatPerfectSupportedWaldhausen ι)
      ((boundedFlatPerfectSupportedTensorUnitRows ι).obj K) :=
  (oneDiagram_isRow (boundedFlatPerfectSupportedWaldhausen ι) _).of_iso _
    (supportedTensorUnitRowDiagramIso ι K).symm

end Quillen.PerfectComplexes
