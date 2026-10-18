/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictDiagramHomotopy
public import Quillen.Topology.Prespectrum.HomotopyPushout

/-!
# The forward Bass comparison for the original pointwise pushout

The original whole overlap cylinder is mapped by the actual Bass homotopy action.
Its two endpoint casts are the functor composition equations. Descending these
three unchanged pieces gives the coefficient-natural forward comparison.

This is an adopted independent reconstruction after workspace loss, not historical byte recovery.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u v w
namespace Quillen.KTheory.Bass.PushoutStrength

variable {C : Type u} [Category.{v} C]
  {F₀ F₁ F₂ : C ⥤ LoopPrespectrum.{w}} (f : F₀ ⟶ F₁) (g : F₀ ⟶ F₂)

/-- The actual pointwise reduced homotopy pushout diagram. -/
def pushout : C ⥤ LoopPrespectrum.{w} where
  obj X := HomotopyPushout.prespectrum (f.app X) (g.app X)
  map {X Y} k := HomotopyPushout.map (f.app X) (g.app X) (f.app Y) (g.app Y)
    (F₀.map k) (F₁.map k) (F₂.map k) (f.naturality k).symm (g.naturality k).symm
  map_id X := by
    apply HomotopyPushout.hom_ext
    · apply Hom.ext
      funext n
      ext x
      change HomotopyPushout.left (f.app X) (g.app X) n ((F₁.map (𝟙 X)).map n x) =
        HomotopyPushout.left (f.app X) (g.app X) n x
      rw [F₁.map_id]
      rfl
    · apply Hom.ext
      funext n
      ext x
      change HomotopyPushout.right (f.app X) (g.app X) n ((F₂.map (𝟙 X)).map n x) =
        HomotopyPushout.right (f.app X) (g.app X) n x
      rw [F₂.map_id]
      rfl
    · intro n r x
      change HomotopyPushout.cylinder (f.app X) (g.app X) n (r, (F₀.map (𝟙 X)).map n x) =
        HomotopyPushout.cylinder (f.app X) (g.app X) n (r, x)
      rw [F₀.map_id]
      rfl
  map_comp k l := by simp only [Functor.map_comp, HomotopyPushout.map_comp]

/-- The unchanged left inclusion. -/
def left : F₁ ⟶ pushout f g where
  app X := HomotopyPushout.inl (f.app X) (g.app X)
  naturality _X _Y k := (HomotopyPushout.inl_map _ _ _ _ _ _ _
    (f.naturality k).symm (g.naturality k).symm).symm

/-- The unchanged right inclusion. -/
def right : F₂ ⟶ pushout f g where
  app X := HomotopyPushout.inr (f.app X) (g.app X)
  naturality _X _Y k := (HomotopyPushout.inr_map _ _ _ _ _ _ _
    (f.naturality k).symm (g.naturality k).symm).symm

/-- The original whole overlap, with transformation endpoints. -/
def glue (X : C) : Homotopy ((f ≫ left f g).app X) ((g ≫ right f g).app X) :=
  HomotopyPushout.glue (f.app X) (g.app X)

/-- The original overlap is coefficient-natural at the identical time. -/
theorem glue_naturality {X Y : C} (k : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : (F₀.obj X).space n) :
    ((pushout f g).map k).map n ((glue f g X).level n (r, x)) =
      (glue f g Y).level n (r, (F₀.map k).map n x) := rfl

variable (Q : C ⥤ Arrow (Arrow C))

/-- Bass acts on the entire original overlap; only endpoint witnesses are cast. -/
def bassGlue (X : C) :
    Homotopy ((((strictDiagramFunctor Q).map f).app X) ≫
        (((strictDiagramFunctor Q).map (left f g)).app X))
      ((((strictDiagramFunctor Q).map g).app X) ≫
        (((strictDiagramFunctor Q).map (right f g)).app X)) :=
  (strictDiagramMapHomotopy (glue f g) (glue_naturality f g) Q X).cast
    (congrArg (fun a => a.app X) ((strictDiagramFunctor Q).map_comp f (left f g)))
    (congrArg (fun a => a.app X) ((strictDiagramFunctor Q).map_comp g (right f g)))

/-- The original quotient descent defining the forward comparison. -/
def comparison (X : C) :
    HomotopyPushout.prespectrum (((strictDiagramFunctor Q).map f).app X)
      (((strictDiagramFunctor Q).map g).app X) ⟶
        (((strictDiagramFunctor Q).obj (pushout f g)).obj X) :=
  HomotopyPushout.desc _ _ (((strictDiagramFunctor Q).map (left f g)).app X)
    (((strictDiagramFunctor Q).map (right f g)).app X) (bassGlue f g Q X)

/-- The comparison retains the original left inclusion. -/
@[reassoc]
theorem comparison_left (X : C) :
    HomotopyPushout.inl (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map g).app X) ≫ comparison f g Q X =
      (((strictDiagramFunctor Q).map (left f g)).app X) :=
  HomotopyPushout.inl_desc _ _ _ _ _

/-- The comparison retains the original right inclusion. -/
@[reassoc]
theorem comparison_right (X : C) :
    HomotopyPushout.inr (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map g).app X) ≫ comparison f g Q X =
      (((strictDiagramFunctor Q).map (right f g)).app X) :=
  HomotopyPushout.inr_desc _ _ _ _ _

/-- Every value of the original overlap is the Bass image of that same whole track. -/
theorem comparison_overlap (X : C) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F₀).obj X).space n) :
    (comparison f g Q X).map n
      (HomotopyPushout.cylinder (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map g).app X) n (r, x)) =
      (strictDiagramMapHomotopy (glue f g) (glue_naturality f g) Q X).level n (r, x) := rfl

/-- The actual comparison commutes with every coefficient arrow. -/
theorem comparison_naturality {X Y : C} (k : X ⟶ Y) :
    (pushout ((strictDiagramFunctor Q).map f) ((strictDiagramFunctor Q).map g)).map k ≫
        comparison f g Q Y =
      comparison f g Q X ≫ ((strictDiagramFunctor Q).obj (pushout f g)).map k := by
  apply HomotopyPushout.hom_ext
  · apply Hom.ext
    funext n
    ext x
    change (((strictDiagramFunctor Q).map (left f g)).app Y).map n
      ((((strictDiagramFunctor Q).obj F₁).map k).map n x) =
      (((strictDiagramFunctor Q).obj (pushout f g)).map k).map n
        ((((strictDiagramFunctor Q).map (left f g)).app X).map n x)
    exact congrArg (fun a => a.map n x)
      (((strictDiagramFunctor Q).map (left f g)).naturality k)
  · apply Hom.ext
    funext n
    ext x
    change (((strictDiagramFunctor Q).map (right f g)).app Y).map n
      ((((strictDiagramFunctor Q).obj F₂).map k).map n x) =
      (((strictDiagramFunctor Q).obj (pushout f g)).map k).map n
        ((((strictDiagramFunctor Q).map (right f g)).app X).map n x)
    exact congrArg (fun a => a.map n x)
      (((strictDiagramFunctor Q).map (right f g)).naturality k)
  · intro n r x
    exact (strictDiagramMapHomotopy_naturality
      (glue f g) (glue_naturality f g) Q k n r x).symm

/-- The forward comparison is an actual natural transformation of spectrum diagrams. -/
def rho : pushout ((strictDiagramFunctor Q).map f) ((strictDiagramFunctor Q).map g) ⟶
    (strictDiagramFunctor Q).obj (pushout f g) where
  app X := comparison f g Q X
  naturality _X _Y k := comparison_naturality f g Q k

end Quillen.KTheory.Bass.PushoutStrength
