/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.ExactCategory.Isomorphisms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Binary products of exact categories

The product exact structure consists of short complexes whose two projections
are conflations. The projections, pairings and zero insertions are genuine exact
functors. The underlying additive structure and the required limits are formed
componentwise, without an abelian hypothesis.

The intended upstream owner is `Aglib.CategoryTheory.ExactCategory.Product`.
The current consumer is `Quillen.KTheory.FiniteSupport.FiniteProduct`, which
compares the original Quillen projection K-maps with the S-product comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits
open scoped ZeroObject

universe v₁ v₂ v₃ u₁ u₂ u₃ w w'

namespace CategoryTheory.Prod

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- Pair cones over the two projections of one diagram. -/
def pairCone {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    (c : Cone (F ⋙ fst C D)) (d : Cone (F ⋙ snd C D)) : Cone F where
  pt := (c.pt, d.pt)
  π := { app := fun j => (c.π.app j, d.π.app j)
         naturality := fun i j f => by
           exact _root_.Prod.ext (by simpa using (c.w f).symm)
             (by simpa using (d.w f).symm) }

/-- Pair cocones over the two projections of one diagram. -/
def pairCocone {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    (c : Cocone (F ⋙ fst C D)) (d : Cocone (F ⋙ snd C D)) : Cocone F where
  pt := (c.pt, d.pt)
  ι := { app := fun j => (c.ι.app j, d.ι.app j)
         naturality := fun i j f => by
           exact _root_.Prod.ext (by simpa using c.w f) (by simpa using d.w f) }

/-- A cone in a product is limiting when both projections are limiting. -/
def isLimitOfProjections {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cone F} (hc : IsLimit ((fst C D).mapCone c))
    (hd : IsLimit ((snd C D).mapCone c)) : IsLimit c where
  lift s := (hc.lift ((fst C D).mapCone s), hd.lift ((snd C D).mapCone s))
  fac s j := _root_.Prod.ext (hc.fac ((fst C D).mapCone s) j) (hd.fac ((snd C D).mapCone s) j)
  uniq s m hm := _root_.Prod.ext
    (hc.uniq ((fst C D).mapCone s) m.1 (fun j => congrArg _root_.Prod.fst (hm j)))
    (hd.uniq ((snd C D).mapCone s) m.2 (fun j => congrArg _root_.Prod.snd (hm j)))

/-- A cocone in a product is colimiting when both projections are colimiting. -/
def isColimitOfProjections {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cocone F} (hc : IsColimit ((fst C D).mapCocone c))
    (hd : IsColimit ((snd C D).mapCocone c)) : IsColimit c where
  desc s := (hc.desc ((fst C D).mapCocone s), hd.desc ((snd C D).mapCocone s))
  fac s j := _root_.Prod.ext (hc.fac ((fst C D).mapCocone s) j)
    (hd.fac ((snd C D).mapCocone s) j)
  uniq s m hm := _root_.Prod.ext
    (hc.uniq ((fst C D).mapCocone s) m.1 (fun j => congrArg _root_.Prod.fst (hm j)))
    (hd.uniq ((snd C D).mapCocone s) m.2 (fun j => congrArg _root_.Prod.snd (hm j)))

instance hasLimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D)
    [HasLimit (F ⋙ fst C D)] [HasLimit (F ⋙ snd C D)] : HasLimit F :=
  ⟨⟨pairCone (limit.cone _) (limit.cone _),
    isLimitOfProjections (limit.isLimit _) (limit.isLimit _)⟩⟩

instance hasColimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D)
    [HasColimit (F ⋙ fst C D)] [HasColimit (F ⋙ snd C D)] : HasColimit F :=
  ⟨⟨pairCocone (colimit.cocone _) (colimit.cocone _),
    isColimitOfProjections (colimit.isColimit _) (colimit.isColimit _)⟩⟩

instance hasLimitsOfShape {J : Type w} [Category.{w'} J]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D] : HasLimitsOfShape J (C × D) where
  has_limit _ := inferInstance

instance hasColimitsOfShape {J : Type w} [Category.{w'} J]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D] : HasColimitsOfShape J (C × D) where
  has_colimit _ := inferInstance

/-- First projection preserves a displayed limit. -/
def isLimitFst {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cone F} (h : IsLimit c) : IsLimit ((fst C D).mapCone c) where
  lift s := (h.lift (pairCone s ((snd C D).mapCone c))).1
  fac s j := congrArg _root_.Prod.fst (h.fac (pairCone s ((snd C D).mapCone c)) j)
  uniq s m hm := congrArg _root_.Prod.fst (h.uniq
    (pairCone s ((snd C D).mapCone c)) (m, 𝟙 c.pt.2)
    (fun j => _root_.Prod.ext (hm j) (Category.id_comp _)))

/-- Second projection preserves a displayed limit. -/
def isLimitSnd {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cone F} (h : IsLimit c) : IsLimit ((snd C D).mapCone c) where
  lift s := (h.lift (pairCone ((fst C D).mapCone c) s)).2
  fac s j := congrArg _root_.Prod.snd (h.fac (pairCone ((fst C D).mapCone c) s) j)
  uniq s m hm := congrArg _root_.Prod.snd (h.uniq
    (pairCone ((fst C D).mapCone c) s) (𝟙 c.pt.1, m)
    (fun j => _root_.Prod.ext (Category.id_comp _) (hm j)))

/-- First projection preserves a displayed colimit. -/
def isColimitFst {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cocone F} (h : IsColimit c) : IsColimit ((fst C D).mapCocone c) where
  desc s := (h.desc (pairCocone s ((snd C D).mapCocone c))).1
  fac s j := congrArg _root_.Prod.fst (h.fac (pairCocone s ((snd C D).mapCocone c)) j)
  uniq s m hm := congrArg _root_.Prod.fst (h.uniq
    (pairCocone s ((snd C D).mapCocone c)) (m, 𝟙 c.pt.2)
    (fun j => _root_.Prod.ext (hm j) (Category.comp_id _)))

/-- Second projection preserves a displayed colimit. -/
def isColimitSnd {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cocone F} (h : IsColimit c) : IsColimit ((snd C D).mapCocone c) where
  desc s := (h.desc (pairCocone ((fst C D).mapCocone c) s)).2
  fac s j := congrArg _root_.Prod.snd (h.fac (pairCocone ((fst C D).mapCocone c) s) j)
  uniq s m hm := congrArg _root_.Prod.snd (h.uniq
    (pairCocone ((fst C D).mapCocone c) s) (𝟙 c.pt.1, m)
    (fun j => _root_.Prod.ext (Category.comp_id _) (hm j)))

instance fst_preservesLimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D) :
    PreservesLimit F (fst C D) where
  preserves h := ⟨isLimitFst h⟩

instance snd_preservesLimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D) :
    PreservesLimit F (snd C D) where
  preserves h := ⟨isLimitSnd h⟩

instance fst_preservesColimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D) :
    PreservesColimit F (fst C D) where
  preserves h := ⟨isColimitFst h⟩

instance snd_preservesColimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D) :
    PreservesColimit F (snd C D) where
  preserves h := ⟨isColimitSnd h⟩

variable [Preadditive C] [Preadditive D]

instance preadditive : Preadditive (C × D) where
  homGroup P Q := inferInstanceAs (AddCommGroup ((P.1 ⟶ Q.1) × (P.2 ⟶ Q.2)))
  add_comp _ _ _ _ _ _ := _root_.Prod.ext
    (Preadditive.add_comp _ _ _ _ _ _) (Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ _ _ _ := _root_.Prod.ext
    (Preadditive.comp_add _ _ _ _ _ _) (Preadditive.comp_add _ _ _ _ _ _)

instance fst_additive : (fst C D).Additive where
  map_add := rfl

instance snd_additive : (snd C D).Additive where
  map_add := rfl

instance hasFiniteBiproducts [HasFiniteBiproducts C] [HasFiniteBiproducts D] :
    HasFiniteBiproducts (C × D) := by
  have : HasFiniteProducts (C × D) := ⟨fun _ => inferInstance⟩
  exact HasFiniteBiproducts.of_hasFiniteProducts

end CategoryTheory.Prod

namespace CategoryTheory.ExactCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]

namespace ExactStructure

variable (E : ExactStructure C) (F : ExactStructure D)

/-- Componentwise conflations in the binary product. -/
def productConflation (S : ShortComplex (C × D)) : Prop :=
  E.conflation (S.map (Prod.fst C D)) ∧ F.conflation (S.map (Prod.snd C D))

lemma productConflation_inflation_iff {X Y : C × D} (i : X ⟶ Y) :
    Conflations.inflation (C × D) (E.productConflation F) i ↔
      E.inflation i.1 ∧ F.inflation i.2 := by
  constructor
  · rintro ⟨Z, p, h, hS⟩
    exact ⟨⟨Z.1, p.1, congrArg _root_.Prod.fst h, hS.1⟩,
      ⟨Z.2, p.2, congrArg _root_.Prod.snd h, hS.2⟩⟩
  · rintro ⟨⟨Z, p, h, hS⟩, ⟨Z', p', h', hS'⟩⟩
    exact ⟨(Z, Z'), (p, p'), _root_.Prod.ext h h', hS, hS'⟩

lemma productConflation_deflation_iff {X Y : C × D} (p : X ⟶ Y) :
    Conflations.deflation (C × D) (E.productConflation F) p ↔
      E.deflation p.1 ∧ F.deflation p.2 := by
  constructor
  · rintro ⟨Z, i, h, hS⟩
    exact ⟨⟨Z.1, i.1, congrArg _root_.Prod.fst h, hS.1⟩,
      ⟨Z.2, i.2, congrArg _root_.Prod.snd h, hS.2⟩⟩
  · rintro ⟨⟨Z, i, h, hS⟩, ⟨Z', i', h', hS'⟩⟩
    exact ⟨(Z, Z'), (i, i'), _root_.Prod.ext h h', hS, hS'⟩

/-- The binary product exact structure, with componentwise conflations. -/
def prod : ExactStructure (C × D) where
  conflation := E.productConflation F
  kernel S h := Prod.isLimitOfProjections
    ((KernelFork.isLimitMapConeEquiv _ _).symm (E.kernel _ h.1))
    ((KernelFork.isLimitMapConeEquiv _ _).symm (F.kernel _ h.2))
  cokernel S h := Prod.isColimitOfProjections
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm (E.cokernel _ h.1))
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm (F.cokernel _ h.2))
  iso_closed e h := ⟨E.iso_closed ((Prod.fst C D).mapShortComplex.mapIso e) h.1,
    F.iso_closed ((Prod.snd C D).mapShortComplex.mapIso e) h.2⟩
  inflation_id X := (productConflation_inflation_iff E F _).2
    ⟨E.inflation_id X.1, F.inflation_id X.2⟩
  deflation_id X := (productConflation_deflation_iff E F _).2
    ⟨E.deflation_id X.1, F.deflation_id X.2⟩
  inflation_comp i j hi hj := (productConflation_inflation_iff E F _).2
    ⟨E.inflation_comp _ _ ((productConflation_inflation_iff E F _).1 hi).1
      ((productConflation_inflation_iff E F _).1 hj).1,
     F.inflation_comp _ _ ((productConflation_inflation_iff E F _).1 hi).2
      ((productConflation_inflation_iff E F _).1 hj).2⟩
  deflation_comp p q hp hq := (productConflation_deflation_iff E F _).2
    ⟨E.deflation_comp _ _ ((productConflation_deflation_iff E F _).1 hp).1
      ((productConflation_deflation_iff E F _).1 hq).1,
     F.deflation_comp _ _ ((productConflation_deflation_iff E F _).1 hp).2
      ((productConflation_deflation_iff E F _).1 hq).2⟩
  inflation_hasPushouts := ⟨by
    intro X Y Z i f hi
    have h := (productConflation_inflation_iff E F _).1 hi
    have : HasPushout ((Prod.fst C D).map i) ((Prod.fst C D).map f) :=
      E.inflation.hasPushout f.1 h.1
    have : HasPushout ((Prod.snd C D).map i) ((Prod.snd C D).map f) :=
      F.inflation.hasPushout f.2 h.2
    have : HasColimit (span i f ⋙ Prod.fst C D) :=
      hasColimit_of_iso (spanCompIso (Prod.fst C D) i f)
    have : HasColimit (span i f ⋙ Prod.snd C D) :=
      hasColimit_of_iso (spanCompIso (Prod.snd C D) i f)
    infer_instance⟩
  inflation_cobaseChange := ⟨by
    intro A A' B B' f g f' g' sq hf
    have h := (productConflation_inflation_iff E F _).1 hf
    exact (productConflation_inflation_iff E F _).2
      ⟨E.inflation.of_isPushout (sq.map (Prod.fst C D)) h.1,
        F.inflation.of_isPushout (sq.map (Prod.snd C D)) h.2⟩⟩
  deflation_hasPullbacks := ⟨by
    intro X Y Z p f hp
    have h := (productConflation_deflation_iff E F _).1 hp
    have : HasPullback ((Prod.fst C D).map p) ((Prod.fst C D).map f) :=
      E.deflation.hasPullback f.1 h.1
    have : HasPullback ((Prod.snd C D).map p) ((Prod.snd C D).map f) :=
      F.deflation.hasPullback f.2 h.2
    have : HasLimit (cospan p f ⋙ Prod.fst C D) :=
      hasLimit_of_iso (cospanCompIso (Prod.fst C D) p f).symm
    have : HasLimit (cospan p f ⋙ Prod.snd C D) :=
      hasLimit_of_iso (cospanCompIso (Prod.snd C D) p f).symm
    infer_instance⟩
  deflation_baseChange := ⟨by
    intro X Y Y' S f g f' g' sq hg
    have h := (productConflation_deflation_iff E F _).1 hg
    exact (productConflation_deflation_iff E F _).2
      ⟨E.deflation.of_isPullback (sq.map (Prod.fst C D)) h.1,
        F.deflation.of_isPullback (sq.map (Prod.snd C D)) h.2⟩⟩

@[simp] lemma prod_conflation (S : ShortComplex (C × D)) :
    (E.prod F).conflation S ↔
      E.conflation (S.map (Prod.fst C D)) ∧ F.conflation (S.map (Prod.snd C D)) := Iff.rfl

@[simp] lemma prod_inflation_iff {X Y : C × D} (i : X ⟶ Y) :
    (E.prod F).inflation i ↔ E.inflation i.1 ∧ F.inflation i.2 :=
  E.productConflation_inflation_iff F i

@[simp] lemma prod_deflation_iff {X Y : C × D} (p : X ⟶ Y) :
    (E.prod F).deflation p ↔ E.deflation p.1 ∧ F.deflation p.2 :=
  E.productConflation_deflation_iff F p

/-- The first ordinary product projection is exact. -/
def fstExact : ExactFunctor (E.prod F) E where
  toFunctor := Prod.fst C D
  map_conflation _ h := h.1

/-- The second ordinary product projection is exact. -/
def sndExact : ExactFunctor (E.prod F) F where
  toFunctor := Prod.snd C D
  map_conflation _ h := h.2

end ExactStructure

namespace ExactFunctor

/-- The constant functor at the actual chosen zero object is exact. -/
def zero (E : ExactStructure C) (F : ExactStructure D) : ExactFunctor E F where
  toFunctor := (Functor.const C).obj (0 : D)
  additive := { map_add := (isZero_zero D).eq_of_src _ _ }
  map_conflation _ _ := F.conflation_of_isKernel _
    (KernelFork.IsLimit.ofMonoOfIsZero _ inferInstance (isZero_zero D)) (F.deflation_id _)

variable {T : Type u₃} [Category.{v₃} T] [Preadditive T] [HasFiniteBiproducts T]
  {E : ExactStructure C} {F : ExactStructure D} {G : ExactStructure T}

/-- Pair two exact functors with the same source. -/
def pair (f : ExactFunctor E F) (g : ExactFunctor E G) : ExactFunctor E (F.prod G) where
  toFunctor := f.toFunctor.prod' g.toFunctor
  additive := { map_add := _root_.Prod.ext (f.toFunctor.map_add) (g.toFunctor.map_add) }
  map_conflation S h := ⟨f.map_conflation S h, g.map_conflation S h⟩

end ExactFunctor

namespace ExactStructure

variable (E : ExactStructure C) (F : ExactStructure D)

/-- Insert the first factor and the chosen zero of the second factor. -/
def inlExact : ExactFunctor E (E.prod F) :=
  (ExactFunctor.id E).pair (ExactFunctor.zero E F)

/-- Insert the second factor and the chosen zero of the first factor. -/
def inrExact : ExactFunctor F (E.prod F) :=
  (ExactFunctor.zero F E).pair (ExactFunctor.id F)

@[simp] theorem inlExact_comp_fstExact :
    (E.inlExact F).comp (E.fstExact F) = ExactFunctor.id E := rfl

@[simp] theorem inlExact_comp_sndExact :
    (E.inlExact F).comp (E.sndExact F) = ExactFunctor.zero E F := rfl

@[simp] theorem inrExact_comp_fstExact :
    (E.inrExact F).comp (E.fstExact F) = ExactFunctor.zero F E := rfl

@[simp] theorem inrExact_comp_sndExact :
    (E.inrExact F).comp (E.sndExact F) = ExactFunctor.id F := rfl

end ExactStructure

end CategoryTheory.ExactCategory

