/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SectionChangeIndexModel
public import Quillen.Waldhausen.SConstruction.Iterated.Prespectrum

/-! The actual exact Model comparison induces a strict natural prespectrum comparison. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open CategoryTheory.SectionChangeIndex Quillen.Waldhausen.IteratedS.SectionChangeIndex Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.SectionChangeIndexModel
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : Pseudofunctor (LocallyDiscrete D) Cat.{u, u})
    (W : ∀ d, Quillen.Waldhausen.Structure (F.obj ⟨d⟩))
    (Z : ∀ d, F.obj ⟨d⟩) (hZ : ∀ d, IsZero (Z d))
    (hmap : ∀ {d e : D} (f : d ⟶ e), IsZero ((F.map f.toLoc).toFunctor.obj (Z d)))
    (K : C ⥤ D)
    (hExact : ∀ {d e : D} (f : d ⟶ e),
      Quillen.Waldhausen.IsExact (W d).cof (W d).weq (W e).cof (W e).weq
        (F.map f.toLoc).toFunctor)

/-- Apply the existing iterated-S prespectrum functor to the actual Model transformation. -/
def restrictionPrespectrum :
    (K ⋙ modelDiagram F W Z hZ hmap hExact) ⋙ prespectrumFunctor ⟶
      modelDiagram (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) (fun {_ _} f => hExact (K.map f)) ⋙
          prespectrumFunctor :=
  Functor.whiskerRight (restrictionModel F W Z hZ hmap K hExact) prespectrumFunctor

/-- The comparison retains the original, explicitly constructed restriction Model map. -/
theorem restrictionPrespectrum_app (c : C) :
    (restrictionPrespectrum F W Z hZ hmap K hExact).app c =
      prespectrumFunctor.map (restrictionModelMap F W Z hZ hmap K c) := rfl

end QuillenTest.SectionChangeIndexModel
