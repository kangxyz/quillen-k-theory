/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Waldhausen.Fibration.InverseImageWeak
public import Quillen.Waldhausen.Fibration.Rows.ComplexRelativeJoint

/-! Semantic consumers for the unchanged source cofibration category and the
quasi-isomorphism-fine relative complex cylinder. All universes are independent. -/
@[expose] public section

open Quillen.Waldhausen


open CategoryTheory.ExactCategory


noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open Quillen Quillen.Waldhausen.Fibration
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section InverseImage
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

example : (Structure.withInverseImageWeak hF).zero = V.zero := rfl
example : (Structure.withInverseImageWeak hF).cof = V.cof := rfl
example {X Y : C} (f : X ⟶ Y) :
    (Structure.withInverseImageWeak hF).weq f ↔ W.weq (F.map f) := Iff.rfl
example {X Y : C} (f : X ⟶ Y) (hf : V.weq f) :
    (Structure.inverseImageWeakNested hF).coarse.weq f :=
  (Structure.inverseImageWeakNested hF).le_weq _ hf
example [W.weq.HasTwoOutOfThreeProperty] :
    (Structure.withInverseImageWeak hF).weq.HasTwoOutOfThreeProperty := inferInstance
example (he : ExtensionAxiom W) : ExtensionAxiom (Structure.withInverseImageWeak hF) :=
  Structure.withInverseImageWeak_extensionAxiom hF he
example : IsExact V.cof V.weq (Structure.withInverseImageWeak hF).cof
    (Structure.withInverseImageWeak hF).weq (𝟭 C) :=
  changeWeak_exact (Structure.inverseImageWeakNested hF)
example : IsExact (Structure.withInverseImageWeak hF).cof
    (Structure.withInverseImageWeak hF).weq W.cof W.weq F :=
  Structure.withInverseImageWeak_exact hF

-- The source still supplies the exact same displayed pushouts and cofibrations.
example {A B D P : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P}
    (hi : V.cof i) (hp : IsPushout i f g j) : (Structure.withInverseImageWeak hF).cof j :=
  (Structure.withInverseImageWeak hF).cof_pushout hi hp

end InverseImage
section Complexes
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))
  (N : NestedWeakEquivalences (complexSubcategory P))

example : IsExact (ArrowCategory.waldhausenStructure (complexSubcategory P)).cof
    (ArrowCategory.waldhausenStructure (complexSubcategory P)).weq
    (ExtensionCategory.waldhausenStructure (complexSubcategory P)).cof
    (ExtensionCategory.waldhausenStructure (complexSubcategory P)).weq
    (complexJointDataOfNested P hcone hshift N).joint :=
  (complexJointDataOfNested P hcone hshift N).exact

example (f : Arrow P.FullSubcategory) :
    N.coarse.weq ((complexJointDataOfNested P hcone hshift N).projection.app f) :=
  (complexJointDataOfNested P hcone hshift N).weak f

example {n : SimplexCategory} (f : Arrow (QuotientRows.Obj (complexSubcategory P) n)) :
    QuotientRows.cof (complexSubcategory P) n
      ((complexRowFactorizationOfNested P hcone hshift N n).inclusion.app f) :=
  (complexRowFactorizationOfNested P hcone hshift N n).cofibration f

example {n : SimplexCategory} (f : Arrow (QuotientRows.Obj (complexSubcategory P) n))
    (p : Interval n) :
    QuasiIso (((complexRowFactorizationOfNested P hcone hshift N n).projection.app f).hom.app p).hom
      :=
  (complexSubcategoryFactorization P hcone).weak (Arrow.mk (f.hom.hom.app p))

example {n : SimplexCategory} (f : Arrow (QuotientRows.Obj (complexSubcategory P) n)) :
    (RowFactorization.targetInclusion N (complexJointDataOfNested P hcone hshift N) n).app f ≫
      (complexRowFactorizationOfNested P hcone hshift N n).projection.app f = 𝟙 f.right :=
  RowFactorization.targetInclusion_projection N (complexJointDataOfNested P hcone hshift N)
    (complexJointDataOfNested_secondEndpointSection P hcone hshift N) f

example [N.coarse.weq.HasTwoOutOfThreeProperty] {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj (complexSubcategory P) n)) :
    (RowWeakEquivalences.coarseStructure N n).weq
      ((RowFactorization.targetInclusion N (complexJointDataOfNested P hcone hshift N) n).app f) :=
  RowFactorization.targetInclusion_weak N (complexJointDataOfNested P hcone hshift N)
    (complexJointDataOfNested_secondEndpointSection P hcone hshift N) f

example {D : Type u'} [Category.{v'} D] {W : Structure D} {F : P.FullSubcategory ⥤ D}
    (hF : IsExact (complexSubcategory P).cof (complexSubcategory P).weq W.cof W.weq F)
    (f : Arrow P.FullSubcategory) :
    W.weq (F.map ((complexJointDataOfNested P hcone hshift
      (Structure.inverseImageWeakNested hF)).projection.app f)) :=
  (complexJointDataOfNested P hcone hshift (Structure.inverseImageWeakNested hF)).weak f

end Complexes
