/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic


public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.Algebra.Homology.Embedding.CochainComplex.TruncGE
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Homology
public import Quillen.AlgebraicGeometry.PerfectComplexes.OppositeJointData
public import Quillen.Waldhausen.Fibration.Rows.BaseFactorization
public import Quillen.Waldhausen.Approximation.GeneralKEquivalence
public import Quillen.Waldhausen.Duality.SConstruction
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# Original lower-bounded perfect-complex comparison

For compact schemes, the literal lower-bounded inclusion retains the original
K-map in every degree. This module uses no Godement premise.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory

open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry HomologicalComplex
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.BoundedBelow

variable {X : Scheme.{u}}

/-- The complex-subcategory Waldhausen structure on lower-bounded locally perfect complexes. -/
def waldhausen (X : Scheme.{u}) : Waldhausen.Structure (Obj X) :=
  Waldhausen.complexSubcategory (objects X)

lemma inclusion_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (waldhausen X).cof (waldhausen X).weq
    (perfectWaldhausen X).cof (perfectWaldhausen X).weq (inclusion X) :=
  Waldhausen.subcategoryInclusion_exact _ _ (fun _ h => h.1)

/-- The opposite complex-subcategory Waldhausen structure for lower-bounded perfect complexes. -/
def oppositeWaldhausen (X : Scheme.{u}) : Waldhausen.Structure (Obj X)ᵒᵖ :=
  Waldhausen.oppositeComplexSubcategory (objects X)

lemma opposite_compatible (X : Scheme.{u}) :
    Waldhausen.IsCompatibleDual (waldhausen X) (oppositeWaldhausen X) :=
  Waldhausen.oppositeComplexSubcategory_compatible (objects X)

lemma inclusion_op_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (oppositeWaldhausen X).cof (oppositeWaldhausen X).weq
    (perfectOppositeWaldhausen X).cof (perfectOppositeWaldhausen X).weq
    (inclusion X).op :=
  Waldhausen.oppositeSubcategoryInclusion_exact _ _ (fun _ h => h.1)

/-- Joint row-factorization data for the opposite structure, using closure under shift by `-1`. -/
def oppositeJointData (X : Scheme.{u}) :
    Waldhausen.Fibration.RowFactorization.JointData
      (Waldhausen.Fibration.NestedWeakEquivalences.refl (oppositeWaldhausen X)) :=
  Waldhausen.oppositeComplexJointData (objects X) (fun _ h => objects_shift h (-1))

/-- Actual App2 in the literal opposite categories; the original arrow is retained. -/
theorem inclusion_op_approximation (X : Scheme.{u}) [CompactSpace X] :
    Waldhausen.HasApproximationProperty (oppositeWaldhausen X)
      (perfectOppositeWaldhausen X) (inclusion X).op where
  reflects _ h := h
  lift {K L} f := by
    obtain ⟨b, c, hbc⟩ := locallyPerfect_homology_bounded L.unop.property
    obtain ⟨d, hd⟩ := K.unop.property.2
    let := hd
    let a := min b d
    have hKa : K.unop.obj.IsStrictlyGE a :=
      K.unop.obj.isStrictlyGE_of_ge a d (min_le_right _ _)
    let := hKa
    have hLa : L.unop.obj.IsGE a := (CochainComplex.isGE_iff _ _).mpr (fun n hn =>
      (exactAt_iff_isZero_homology _ _).mpr (hbc n (Or.inl (by dsimp [a] at hn; omega))))
    let := hLa
    let T : Obj X := ⟨L.unop.obj.truncGE a,
      (locallyPerfect_iff_of_quasiIso (L.unop.obj.πTruncGE a)).mp L.unop.property,
      a, inferInstance⟩
    let s : L.unop.obj ⟶ K.unop.obj := f.unop.hom
    let g : T ⟶ K.unop := ObjectProperty.homMk (CochainComplex.fromTruncGE s a)
    let η : L.unop ⟶ (inclusion X).obj T :=
      ObjectProperty.homMk (L.unop.obj.πTruncGE a)
    have hη : (perfectWaldhausen X).weq η := by
      change QuasiIso (L.unop.obj.πTruncGE a)
      infer_instance
    have hfac : η ≫ (inclusion X).map g = f.unop := by
      apply ObjectProperty.hom_ext
      exact CochainComplex.πTruncGE_fromTruncGE s a
    let D := (oppositeJointData X).sourceFactorization
    let A := Arrow.mk g.op
    let i := D.inclusion.app A
    let q := D.projection.app A
    refine ⟨D.middle.obj A, i, (inclusion X).op.map q ≫ η.op, D.cofibration A, ?_, ?_⟩
    · exact (perfectOppositeWaldhausen X).weq.comp_mem _ _
        ((inclusion_op_exact X).weak q (D.weak A)) hη
    · rw [← Category.assoc, ← Functor.map_comp, D.factorization A]
      exact congrArg Quiver.Hom.op hfac

/-- The unchanged original S-map is weak by actual opposite approximation and S-duality. -/
theorem inclusion_delooping_weak (X : Scheme.{u}) [CompactSpace X] :
    IsWeakHomotopyEquivalence (Waldhausen.deloopingMap (inclusion_exact X)).hom := by
  let : (perfectOppositeWaldhausen X).weq.HasTwoOutOfThreeProperty := by
    change ((perfectWaldhausen X).weq.op).HasTwoOutOfThreeProperty
    let : (perfectWaldhausen X).weq.HasTwoOutOfThreeProperty :=
      Waldhausen.complexSubcategory_saturated (locallyPerfect X)
    infer_instance
  have hd := (inclusion_op_approximation X).deloopingMap_isWeakHomotopyEquivalence_general
    (inclusion_op_exact X) (oppositeJointData X)
  exact Waldhausen.DualSConstruction.sSetMap_weak_of_dual
    (opposite_compatible X) (perfectOppositeWaldhausen_compatible X)
    (inclusion_exact X) (inclusion_op_exact X) hd

/-- The literal original inclusion K-map is bijective in every degree, including zero. -/
theorem inclusion_KMap_bijective (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    Function.Bijective (Waldhausen.KMap (inclusion_exact X) n) :=
  Waldhausen.KMap_bijective_of_isWeakHomotopyEquivalence
    (inclusion_exact X) (inclusion_delooping_weak X) n

end Quillen.PerfectComplexes.BoundedBelow
