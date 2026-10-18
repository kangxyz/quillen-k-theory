/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenPairDiagram
public import Quillen.KTheory.Bass.NaturalModelUnitTrack

/-!
# Original Laurent tracks on the complete scheme-parameter localization diagram

These are the original evaluation-lifted units on the ambient category and its
actual supported full subcategory. The relative-open model changes only weakness.
The actual support forgetful map and geometric open restriction preserve every
original scalar-track time.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.ParameterLaurentTrack
open GlobalSectionChangeIndex GlobalSupportedParameter
open ParameterLaurentUnit GeometricSeedCospan NaturalTrack
attribute [local irreducible] globalModel

private theorem preservesIdentity {C : Type*} [Category C] (α : 𝟭 C ≅ 𝟭 C) :
    Preserves (𝟭 C) α α := fun _ => rfl

private theorem preservesRestricted {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (hF : ∀ x : P.FullSubcategory, Q (F.obj x.obj))
    (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) (h : Preserves F α β) :
    Preserves (Q.lift (P.ι ⋙ F) hF) (lift P.ι α) (lift Q.ι β) := by
  intro x
  apply ObjectProperty.hom_ext
  change F.map (((lift P.ι α).hom.app x).hom) =
    ((lift Q.ι β).hom.app ((Q.lift (P.ι ⋙ F) hF).obj x)).hom
  rw [show ((lift P.ι α).hom.app x).hom = α.hom.app x.obj from map_lift_hom P.ι α x,
    show ((lift Q.ι β).hom.app ((Q.lift (P.ι ⋙ F) hF).obj x)).hom =
      β.hom.app (F.obj x.obj) from map_lift_hom Q.ι β _]
  exact h x.obj

/-- The original whole ambient parameter track under every scheme morphism. -/
def ambientTrack (Q : Scheme.{u}) :
    Track laurent.op coefficient (ParameterModels.ambient Q ⋙ prespectrumFunctor) :=
  ofModelUnits laurent.op coefficient (ParameterModels.ambient Q)
    (ambientUnit Q) (ambientUnit_naturality Q)

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original support predicate on each actual parameter ambient category. -/
abbrev parameterSupported (X : Scheme.{u}ᵒᵖ) :
    ObjectProperty ((ParameterModels.ambient Q).obj X) :=
  supported (X := op (pair f X.unop).obj.right) (pair f X.unop).obj.hom

/-- Restrict the same projected global unit to the actual supported full subcategory. -/
def supportedUnit (X : Scheme.{u}ᵒᵖ) :
    𝟭 (parameterSupported f (laurent.op.obj X)).FullSubcategory ≅
      𝟭 (parameterSupported f (laurent.op.obj X)).FullSubcategory :=
  lift (parameterSupported f (laurent.op.obj X)).ι (ambientUnit Q X)

/-- Original supported parameter pullback preserves the same lifted identity unit. -/
theorem supportedUnit_naturality {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves ((ParameterModels.supported f).map (laurent.op.map g)).functor
      (supportedUnit f X) (supportedUnit f Y) :=
  preservesRestricted (parameterSupported f (laurent.op.obj X))
    (parameterSupported f (laurent.op.obj Y)) _
    (fun x => pairReindex_supported (pairMap f (laurent.op.map g).unop) x.obj x.property)
    _ _ (ambientUnit_naturality Q g)

/-- The original whole supported parameter track, with no replacement of support by a fiber. -/
def supportedTrack :
    Track laurent.op coefficient (ParameterModels.supported f ⋙ prespectrumFunctor) :=
  ofModelUnits laurent.op coefficient (ParameterModels.supported f)
    (supportedUnit f) (supportedUnit_naturality f)

/-- The relative-open category retains the original ambient identity unit unchanged. -/
def openUnit (X : Scheme.{u}ᵒᵖ) :
    𝟭 ((ParameterModels.openModel f).obj (laurent.op.obj X)) ≅
      𝟭 ((ParameterModels.openModel f).obj (laurent.op.obj X)) := ambientUnit Q X

/-- The actual relative-open reindexing preserves the same projected parameter unit. -/
theorem openUnit_naturality {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves ((ParameterModels.openModel f).map (laurent.op.map g)).functor
      (openUnit f X) (openUnit f Y) := by
  exact ambientUnit_naturality Q g

/-- The original relative-open whole parameter track. -/
def openTrack :
    Track laurent.op coefficient (ParameterModels.openModel f ⋙ prespectrumFunctor) :=
  ofModelUnits laurent.op coefficient (ParameterModels.openModel f)
    (openUnit f) (openUnit_naturality f)

/-- Forgetting support preserves the actual lifted unit component. -/
theorem forget_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.forget f).app (laurent.op.obj X)).functor
      (supportedUnit f X) (ambientUnit Q X) := by
  have h : Preserves (parameterSupported f (laurent.op.obj X)).ι
      (lift (parameterSupported f (laurent.op.obj X)).ι (ambientUnit Q X))
      (ambientUnit Q X) := fun x =>
    map_lift_hom (parameterSupported f (laurent.op.obj X)).ι (ambientUnit Q X) x
  exact h

/-- The identity change of weak class preserves the original unit literally. -/
theorem changeWeak_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.changeWeak f).app (laurent.op.obj X)).functor
      (ambientUnit Q X) (openUnit f X) := by
  exact preservesIdentity (ambientUnit Q X)

/-- Geometric open restriction preserves the same external parameter Laurent coordinate. -/
theorem openRestriction_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.openRestriction f).app (laurent.op.obj X)).functor
      (openUnit f X) (ambientUnit P X) := ambientUnit_factor f X

/-- Support forget preserves every time of the original parameter scalar track. -/
theorem forget_equivariant :
    Equivariant (supportedTrack f) (ambientTrack Q)
      (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) :=
  ofModelUnits_equivariant _ _ _ _ _ _ _ _ _ (forget_unit f)

/-- The original change of weakness preserves every scalar-track time. -/
theorem changeWeak_equivariant :
    Equivariant (ambientTrack Q) (openTrack f)
      (Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor) :=
  ofModelUnits_equivariant _ _ _ _ _ _ _ _ _ (changeWeak_unit f)

/-- The original geometric restriction preserves every scalar-track time. -/
theorem openRestriction_equivariant :
    Equivariant (openTrack f) (ambientTrack P)
      (Functor.whiskerRight (ParameterModels.openRestriction f) prespectrumFunctor) :=
  ofModelUnits_equivariant _ _ _ _ _ _ _ _ _ (openRestriction_unit f)

end Quillen.PerfectComplexes.ParameterLaurentTrack
