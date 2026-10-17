/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive

/-! # Additive functors commute with extension of a complex by zero -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u v' u' w w'
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive]
  {ι : Type w} {ι' : Type w'} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- The degreewise comparison, including the actual image of the zero object. -/
def mapExtendObjIso (K : HomologicalComplex C c) (i : Option ι) :
    F.obj (HomologicalComplex.extend.X K i) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) i :=
  match i with
  | none => (F.map_isZero (isZero_zero C)).isoZero
  | some _ => Iso.refl _

/-- The canonical complex comparison between termwise functor and extension by zero. -/
def mapHomologicalComplexExtendIso (e : c.Embedding c') :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor D :=
  NatIso.ofComponents
    (fun K ↦ HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ mapExtendObjIso F K (e.r i)) (by
        intro i j hij
        change (mapExtendObjIso F K (e.r i)).hom ≫
            HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) (e.r i) (e.r j) =
          F.map (HomologicalComplex.extend.d K (e.r i) (e.r j)) ≫
            (mapExtendObjIso F K (e.r j)).hom
        cases hi : e.r i with
        | none => exact (F.map_isZero (isZero_zero C)).eq_of_src _ _
        | some i =>
          cases hj : e.r j with
          | none => exact (isZero_zero D).eq_of_tgt _ _
          | some j =>
            change 𝟙 _ ≫ F.map (K.d i j) = F.map (K.d i j) ≫ 𝟙 _
            simp))
    (by
      intro K L φ
      ext i
      change F.map (HomologicalComplex.extend.mapX φ (e.r i)) ≫
          (mapExtendObjIso F L (e.r i)).hom =
        (mapExtendObjIso F K (e.r i)).hom ≫
          HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map φ) (e.r i)
      cases hi : e.r i with
      | none => exact (F.map_isZero (isZero_zero C)).eq_of_src _ _
      | some i =>
        change F.map (φ.f i) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (φ.f i)
        simp)

end CategoryTheory.Functor
