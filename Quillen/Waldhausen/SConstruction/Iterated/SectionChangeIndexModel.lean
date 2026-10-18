/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Quillen.Aglib.CategoryTheory.FiberedCategory.SectionChangeIndexZero
public import Quillen.Waldhausen.EquivalenceStructure
public import Quillen.Waldhausen.ExtensionCategory.ExactTransport
public import Quillen.Waldhausen.SConstruction.Iterated.Category

/-!
# Evaluation-transported section Models under change of index

The input is an actual family of Waldhausen structures and exact transition functors.
The section structures are the existing `ofEquivalence` construction; the global zero family
is retained literally. No geometric exactness or Bass coherence is postulated by this prototype.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckSections
open Quillen.CategoryTheory.GrothendieckZeroSections Quillen.Waldhausen.IteratedS
open CategoryTheory.SectionChangeIndex
universe u
namespace Quillen.Waldhausen.IteratedS.SectionChangeIndex
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : Pseudofunctor (LocallyDiscrete D) Cat.{u, u})
    (W : ∀ d, Waldhausen.Structure (F.obj ⟨d⟩))
    (Z : ∀ d, F.obj ⟨d⟩) (hZ : ∀ d, IsZero (Z d))
    (hmap : ∀ {d e : D} (f : d ⟶ e), IsZero ((F.map f.toLoc).toFunctor.obj (Z d)))

/-- The original fiber classes transported along evaluation, with the global section zero. -/
def sectionWaldhausen (d : D) :
    Waldhausen.Structure (underCocartesian (Pseudofunctor.Grothendieck.forget F) d) :=
  (W d).ofEquivalence (originalEvaluationEquivalence F d) (sectionZero F Z hZ hmap d)
    (hZ d)

/-- Original identity evaluation is exact for the transported classes. -/
theorem evaluation_exact (d : D) :
    Waldhausen.IsExact (sectionWaldhausen F W Z hZ hmap d).cof
      (sectionWaldhausen F W Z hZ hmap d).weq (W d).cof (W d).weq
      (originalEvaluation F d) := Waldhausen.Structure.ofEquivalence_exact _ _ _ _

private theorem exact_of_evaluation
    {A B E : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory E]
    (V : Waldhausen.Structure A) (W : Waldhausen.Structure E) (e : B ≌ E)
    (z : B) (hz : IsZero (e.functor.obj z)) (H : A ⥤ B)
    (h : Waldhausen.IsExact V.cof V.weq W.cof W.weq (H ⋙ e.functor)) :
    Waldhausen.IsExact V.cof V.weq (W.ofEquivalence e z hz).cof
      (W.ofEquivalence e z hz).weq H where
  zero hx := IsZero.of_full_of_faithful_of_isZero e.functor _ (h.zero hx)
  cofibration f hf := h.cofibration f hf
  weak f hf := h.weak f hf
  pushout hi hp := IsPushout.of_map_of_faithful e.functor (h.pushout hi hp)

/-- Original reindexing is exact when the original fiber transition is exact. -/
theorem reindex_exact
    (hExact : ∀ {d e : D} (f : d ⟶ e),
      Waldhausen.IsExact (W d).cof (W d).weq (W e).cof (W e).weq
        (F.map f.toLoc).toFunctor) {d e : D} (f : d ⟶ e) :
    Waldhausen.IsExact (sectionWaldhausen F W Z hZ hmap d).cof
      (sectionWaldhausen F W Z hZ hmap d).weq
      (sectionWaldhausen F W Z hZ hmap e).cof
      (sectionWaldhausen F W Z hZ hmap e).weq
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f) := by
  apply exact_of_evaluation
  exact Waldhausen.ExtensionCategory.isExact_of_natIso _ _
    ((evaluation_exact F W Z hZ hmap d).comp (hExact f))
    ((originalEvaluationTransitionIso F d (Under.mk f)) ≪≫
      eqToIso (originalEvaluation_reindex F d f).symm)

/-- The actual section category, equipped with the evaluation-transported structure. -/
def sectionModel (d : D) : Model.{u} :=
  ⟨Cat.of (underCocartesian (Pseudofunctor.Grothendieck.forget F) d),
    sectionWaldhausen F W Z hZ hmap d⟩

/-- The strict Model diagram retains original reindexing and the chosen global zero. -/
def modelDiagram
    (hExact : ∀ {d e : D} (f : d ⟶ e),
      Waldhausen.IsExact (W d).cof (W d).weq (W e).cof (W e).weq
        (F.map f.toLoc).toFunctor) : D ⥤ Model.{u} where
  obj := sectionModel F W Z hZ hmap
  map f := ⟨underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f,
    reindex_exact F W Z hZ hmap hExact f, reindex_sectionZero F Z hZ hmap f⟩
  map_id d := by
    apply Model.Hom.ext
    exact underCocartesianReindex_id _ d
  map_comp f g := by
    apply Model.Hom.ext
    exact underCocartesianReindex_comp _ f g

variable (K : C ⥤ D)

/-- Actual change of index is exact because its complete evaluation square is equality. -/
theorem restriction_exact (c : C) :
    Waldhausen.IsExact (sectionWaldhausen F W Z hZ hmap (K.obj c)).cof
      (sectionWaldhausen F W Z hZ hmap (K.obj c)).weq
      (sectionWaldhausen (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) c).cof
      (sectionWaldhausen (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) c).weq (underFunctor F K c) := by
  apply exact_of_evaluation
  change Waldhausen.IsExact (sectionWaldhausen F W Z hZ hmap (K.obj c)).cof
    (sectionWaldhausen F W Z hZ hmap (K.obj c)).weq (W (K.obj c)).cof (W (K.obj c)).weq
    (underFunctor F K c ⋙ originalEvaluation (pullback F K) c)
  rw [CategoryTheory.SectionChangeIndex.evaluation]
  exact evaluation_exact F W Z hZ hmap (K.obj c)

/-- The inverse of the actual restriction equivalence is exact for these same structures. -/
theorem restriction_inverse_exact (c : C) :
    Waldhausen.IsExact
      (sectionWaldhausen (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) c).cof
      (sectionWaldhausen (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) c).weq
      (sectionWaldhausen F W Z hZ hmap (K.obj c)).cof
      (sectionWaldhausen F W Z hZ hmap (K.obj c)).weq
      (underFunctor F K c).asEquivalence.inverse := by
  apply exact_of_evaluation
  let e := (underFunctor F K c).asEquivalence
  have hi : e.inverse ⋙ originalEvaluation F (K.obj c) ≅
      originalEvaluation (pullback F K) c :=
    Functor.isoWhiskerLeft e.inverse (eqToIso (evaluation F K c).symm) ≪≫
      e.invFunIdAssoc (originalEvaluation (pullback F K) c)
  exact Waldhausen.ExtensionCategory.isExact_of_natIso _ _
    (evaluation_exact (pullback F K) (fun c => W (K.obj c))
      (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
      (fun {_ _} f => hmap (K.map f)) c) hi.symm

/-- Actual restriction as an exact, strictly chosen-zero-preserving Model map. -/
def restrictionModelMap (c : C) :
    sectionModel F W Z hZ hmap (K.obj c) ⟶
      sectionModel (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) c where
  functor := underFunctor F K c
  exact := restriction_exact F W Z hZ hmap K c
  zero := restriction_sectionZero F K Z hZ hmap c

/-- The lifted Model comparison is strictly natural in every index arrow. -/
def restrictionModel
    (hExact : ∀ {d e : D} (f : d ⟶ e),
      Waldhausen.IsExact (W d).cof (W d).weq (W e).cof (W e).weq
        (F.map f.toLoc).toFunctor) :
    K ⋙ modelDiagram F W Z hZ hmap hExact ⟶
      modelDiagram (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) (fun {_ _} f => hExact (K.map f)) where
  app := restrictionModelMap F W Z hZ hmap K
  naturality _ _ f := by
    apply Model.Hom.ext
    exact reindex_naturality F K f

end Quillen.Waldhausen.IteratedS.SectionChangeIndex
