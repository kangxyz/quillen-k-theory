/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.InverseImageWeak
public import Quillen.Waldhausen.Fibration.ExactChangeWeak
public import Quillen.Waldhausen.SConstruction.Iterated.Category

/-!
# Actual Model diagrams with weak equivalences detected by a transformation

An existing Model natural transformation supplies every functor and strict square.
Only the source weak classes change. The current consumer is actual restriction from global
bounded-flat sections to the original coarse-open coefficient Model diagram.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace Quillen.Waldhausen.IteratedS.InverseImageModelDiagram
variable {I : Type u} [Category.{v} I] {A B : I ⥤ Model.{w}} (S : A ⟶ B)

/-- The same source category, cofibrations and zero, with actual detected weakness. -/
def model (i : I) : Model.{w} :=
  ⟨(A.obj i).category, Structure.withInverseImageWeak (S.app i).exact⟩

/-- The original component now reflects the chosen weak class by definition. -/
def component (i : I) : model S i ⟶ B.obj i where
  functor := (S.app i).functor
  exact := Structure.withInverseImageWeak_exact (S.app i).exact
  zero := (S.app i).zero

/-- Original source transitions are exact for the detected weak classes. -/
theorem map_exact {i j : I} (f : i ⟶ j) :
    IsExact (model S i).waldhausen.cof (model S i).waldhausen.weq
      (model S j).waldhausen.cof (model S j).waldhausen.weq (A.map f).functor := by
  have he : IsExact (Structure.withInverseImageWeak (S.app i).exact).cof
      (Structure.withInverseImageWeak (S.app i).exact).weq
      (B.obj j).waldhausen.cof (B.obj j).waldhausen.weq
      ((A.map f).functor ⋙ (S.app j).functor) := by
    have h := congrArg Model.Hom.functor (S.naturality f)
    change (A.map f).functor ⋙ (S.app j).functor =
      (S.app i).functor ⋙ (B.map f).functor at h
    rw [h]
    exact (component S i).exact.comp (B.map f).exact
  exact {
    zero := (A.map f).exact.zero
    cofibration := (A.map f).exact.cofibration
    weak := fun k hk => he.weak k hk
    pushout := (A.map f).exact.pushout }

/-- The original transitions retain their literal chosen zeros. -/
def map {i j : I} (f : i ⟶ j) : model S i ⟶ model S j where
  functor := (A.map f).functor
  exact := map_exact S f
  zero := (A.map f).zero

/-- The detected source structures form a strict diagram. -/
def diagram : I ⥤ Model.{w} where
  obj := model S
  map := map S
  map_id i := by
    apply Model.Hom.ext
    have h := congrArg Model.Hom.functor (A.map_id i)
    exact h
  map_comp f g := by
    apply Model.Hom.ext
    have h := congrArg Model.Hom.functor (A.map_comp f g)
    exact h

/-- The unchanged original component functors form an actual Model transformation. -/
def restriction : diagram S ⟶ B where
  app := component S
  naturality i j f := by
    apply Model.Hom.ext
    have h := congrArg Model.Hom.functor (S.naturality f)
    exact h

/-- The source identity changes only the weak class. -/
def changeWeak : A ⟶ diagram S where
  app i := {
    functor := 𝟭 _
    exact := Fibration.changeWeak_exact (Structure.inverseImageWeakNested (S.app i).exact)
    zero := rfl }
  naturality i j f := by
    apply Model.Hom.ext
    exact (Functor.comp_id _).trans (Functor.id_comp _).symm

/-- The two actual transformations factor the original map strictly. -/
theorem factor : changeWeak S ≫ restriction S = S := by
  ext i
  apply Model.Hom.ext
  exact Functor.id_comp _

end Quillen.Waldhausen.IteratedS.InverseImageModelDiagram
