/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Shift
public import Aglib.Algebra.Homology.MappingCone.Identity
public import Aglib.Algebra.Homology.MappingCone.Map
public import Aglib.Algebra.Homology.MappingCone.Acyclicity
public import Quillen.Aglib.Algebra.Homology.MappingCone.Biprod

/-!
# The actual identity cone of the flasque perfect model

The literal cone and its signed inclusion/quotient natural maps preserve inherited exactness, original terms and the original acyclic cone sequence.
-/
@[expose] public section

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients


open CochainComplex

open Quillen




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex CochainComplex
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.FlasqueBoundedBelow
open ProjectiveLine.FlasqueCoefficients
variable (X : Scheme.{u})

/-- The literal identity cone stays in the original flasque, lower-bounded perfect model. -/
lemma identityCone_objects (K : Obj X) :
    objects X (identityConeFunctor.obj K.obj) :=
  objects_of_shortExact (CochainComplex.coneSequence_shortExact (A := X.Modules) K.obj) K.property
    (shift_objects K.property 1)

/-- The literal cone of identity and its native original cone maps. -/
def identityCone : Obj X ⥤ Obj X :=
  ObjectProperty.lift _ ((objects X).ι ⋙ identityConeFunctor) (identityCone_objects X)

instance identityCone_additive : (identityCone X).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    exact CochainComplex.mappingCone.map_add (𝟙 K.obj) (𝟙 L.obj)
      f.hom g.hom f.hom g.hom (by simp) (by simp)

/-- The actual identity cone preserves the inherited original conflations. -/
def identityConeExactFunctor : CategoryTheory.ExactCategory.ExactFunctor
    (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
      (CategoryTheory.ExactCategory.abelianExactStructure
      (CochainComplex X.Modules ℤ))
      (objects X))
    (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
      (CategoryTheory.ExactCategory.abelianExactStructure
      (CochainComplex X.Modules ℤ))
      (objects X)) where
  toFunctor := identityCone X
  map_conflation S hS := by
    change ((S.map (objects X).ι).map identityConeFunctor).ShortExact
    exact CochainComplex.identityConeFunctor_shortExact (A := X.Modules) hS

/-- Every original identity cone is acyclic, for arbitrary original flasque-perfect input. -/
lemma identityCone_acyclic (K : Obj X) : ((identityCone X).obj K).obj.Acyclic :=
  CochainComplex.mappingCone_acyclic_of_quasiIso (𝟙 K.obj)

lemma identityCone_zero {K : Obj X} (hK : IsZero K) : IsZero ((identityCone X).obj K) := by
  have hz := identityCone_isZero ((objects X).ι.map_isZero hK)
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  exact hz.eq_of_src _ _

/-- The literal original cone inclusion is natural in all original maps. -/
def coneFirst : 𝟭 (Obj X) ⟶ identityCone X where
  app K := ObjectProperty.homMk (mappingCone.inr (𝟙 K.obj))
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (mappingCone.triangleMap (𝟙 K.obj) (𝟙 L.obj) f.hom f.hom (by simp)).comm₂.symm

/-- The literal signed original cone quotient to the native shifted input is natural. -/
def coneSecond : identityCone X ⟶ modelShift X 1 where
  app K := ObjectProperty.homMk (mappingCone.triangle (𝟙 K.obj)).mor₃
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (mappingCone.triangleMap (𝟙 K.obj) (𝟙 L.obj) f.hom f.hom (by simp)).comm₃.symm

lemma coneFirst_second : coneFirst X ≫ coneSecond X = 0 := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact (mappingCone.triangleRotateShortComplex (𝟙 K.obj)).zero

lemma coneModelSequence_conflation (K : Obj X) :
    (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
      (CategoryTheory.ExactCategory.abelianExactStructure
      (CochainComplex X.Modules ℤ))
      (objects X)).conflation
      (ShortComplex.mk ((coneFirst X).app K) ((coneSecond X).app K)
        (NatTrans.congr_app (coneFirst_second X) K)) :=
  CochainComplex.coneSequence_shortExact (A := X.Modules) K.obj

end Quillen.PerfectComplexes.FlasqueBoundedBelow

end

end
