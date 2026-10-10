/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.ReedyLifting
import Quillen.CategoryTheory.ArrowDiagrams

/-!
# Functorial factorization on genuine Reedy cofibration arrows

The original source-component factorization is followed by an actual relative
pushout and a second original factorization. The resulting comparison square
has a genuine joint latching cofibration and a componentwise weak projection.
Every construction is functorial in the original square, including its cube
maps. No coherent-diagram factorization is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u

namespace Quillen.Waldhausen.FunctorialFactorization
variable {C : Type u} [Category.{v} C] {W : Structure C}
  (T : FunctorialFactorization W)

/-- The original source component of a square of cofibration arrows. -/
abbrev reedySourceArrow : Arrow (ExtensionCategory.Obj W) ⥤ Arrow C :=
  (ExtensionCategory.source W).mapArrow

/-- Only a Waldhausen pushout is needed for the relative intermediate stage. -/
theorem reedyHasPushout (f : Arrow (ExtensionCategory.Obj W)) :
    HasPushout f.left.obj.hom (T.inclusion.app ((reedySourceArrow (W := W)).obj f)) := by
  obtain ⟨P, i, j, hp⟩ := W.pushout_exists f.left.obj.hom
    (T.inclusion.app ((reedySourceArrow (W := W)).obj f)) f.left.property
  exact hp.hasPushout

attribute [local instance] reedyHasPushout

/-- Actual relative pushouts form a functor on the original square category. -/
def reedyLatching : Arrow (ExtensionCategory.Obj W) ⥤ C where
  obj f := pushout f.left.obj.hom (T.inclusion.app ((reedySourceArrow (W := W)).obj f))
  map {f g} φ := pushout.map _ _ _ _ φ.left.hom.right
    (T.middle.map ((reedySourceArrow (W := W)).map φ)) φ.left.hom.left
    φ.left.hom.w.symm (T.inclusion.naturality ((reedySourceArrow (W := W)).map φ)).symm
  map_id f := by
    apply pushout.hom_ext
    · simp
    · simp only [pushout.inr_desc, Category.comp_id]
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  map_comp φ ψ := by
    apply pushout.hom_ext
    · simp [Category.assoc]
    · simp only [pushout.inr_desc, pushout.inr_desc_assoc, Category.assoc]
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc]

/-- The original upper-right component includes into the relative pushout. -/
def reedyLatchingLeft (f : Arrow (ExtensionCategory.Obj W)) :
    f.left.obj.right ⟶ (T.reedyLatching).obj f := pushout.inl _ _

/-- The factored lower-left component includes into the relative pushout. -/
def reedyLatchingRight (f : Arrow (ExtensionCategory.Obj W)) :
    T.middle.obj ((reedySourceArrow (W := W)).obj f) ⟶ (T.reedyLatching).obj f :=
  pushout.inr _ _

/-- The displayed latching square is the genuine original relative pushout. -/
theorem reedyLatching_isPushout (f : Arrow (ExtensionCategory.Obj W)) :
    IsPushout f.left.obj.hom (T.inclusion.app ((reedySourceArrow (W := W)).obj f))
      (T.reedyLatchingLeft f) (T.reedyLatchingRight f) := IsPushout.of_hasPushout _ _

@[reassoc (attr := simp)]
theorem reedyLatchingLeft_naturality {f g : Arrow (ExtensionCategory.Obj W)} (φ : f ⟶ g) :
    T.reedyLatchingLeft f ≫ (T.reedyLatching).map φ =
      φ.left.hom.right ≫ T.reedyLatchingLeft g := pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem reedyLatchingRight_naturality {f g : Arrow (ExtensionCategory.Obj W)} (φ : f ⟶ g) :
    T.reedyLatchingRight f ≫ (T.reedyLatching).map φ =
      T.middle.map ((reedySourceArrow (W := W)).map φ) ≫ T.reedyLatchingRight g :=
  pushout.inr_desc _ _ _

/-- The original commutative square descends to the relative pushout. -/
def reedyDesc (f : Arrow (ExtensionCategory.Obj W)) :
    (T.reedyLatching).obj f ⟶ f.right.obj.right :=
  (T.reedyLatching_isPushout f).desc f.hom.hom.right
    (T.projection.app ((reedySourceArrow (W := W)).obj f) ≫ f.right.obj.hom) (by
      rw [← Category.assoc, T.factorization]
      exact f.hom.hom.w.symm)

@[reassoc (attr := simp)]
theorem reedyLatchingLeft_desc (f : Arrow (ExtensionCategory.Obj W)) :
    T.reedyLatchingLeft f ≫ T.reedyDesc f = f.hom.hom.right :=
  (T.reedyLatching_isPushout f).inl_desc _ _ _

@[reassoc (attr := simp)]
theorem reedyLatchingRight_desc (f : Arrow (ExtensionCategory.Obj W)) :
    T.reedyLatchingRight f ≫ T.reedyDesc f =
      T.projection.app ((reedySourceArrow (W := W)).obj f) ≫ f.right.obj.hom :=
  (T.reedyLatching_isPushout f).inr_desc _ _ _

/-- Descent is strictly natural in the original comparison cube. -/
theorem reedyDesc_naturality {f g : Arrow (ExtensionCategory.Obj W)} (φ : f ⟶ g) :
    (T.reedyLatching).map φ ≫ T.reedyDesc g = T.reedyDesc f ≫ φ.right.hom.right := by
  apply (T.reedyLatching_isPushout f).hom_ext
  · rw [reedyLatchingLeft_naturality_assoc, reedyLatchingLeft_desc,
      reedyLatchingLeft_desc_assoc]
    exact congrArg (fun a ↦ a.hom.right) φ.w
  · rw [reedyLatchingRight_naturality_assoc, reedyLatchingRight_desc,
      reedyLatchingRight_desc_assoc, ← Category.assoc,
      T.projection.naturality, Category.assoc]
    exact congrArg (fun a ↦ T.projection.app ((reedySourceArrow (W := W)).obj f) ≫ a)
      φ.right.hom.w

/-- The actual second factorization problem, naturally in every original square. -/
def reedyTargetArrow : Arrow (ExtensionCategory.Obj W) ⥤ Arrow C where
  obj f := Arrow.mk (T.reedyDesc f)
  map φ := Arrow.homMk ((T.reedyLatching).map φ) φ.right.hom.right
    (T.reedyDesc_naturality φ)
  map_id f := by apply Arrow.hom_ext <;> simp
  map_comp φ ψ := by apply Arrow.hom_ext <;> simp

/-- The structural cofibration between the two genuinely factored vertices. -/
def reedyMiddleInclusion :
    reedySourceArrow (W := W) ⋙ T.middle ⟶ T.reedyTargetArrow ⋙ T.middle where
  app f := T.reedyLatchingRight f ≫ T.inclusion.app (T.reedyTargetArrow.obj f)
  naturality f g φ := by
    change T.middle.map ((reedySourceArrow (W := W)).map φ) ≫
        (T.reedyLatchingRight g ≫ T.inclusion.app (T.reedyTargetArrow.obj g)) =
      (T.reedyLatchingRight f ≫ T.inclusion.app (T.reedyTargetArrow.obj f)) ≫
        T.middle.map (T.reedyTargetArrow.map φ)
    rw [← Category.assoc, ← reedyLatchingRight_naturality, Category.assoc]
    have hn := T.inclusion.naturality (T.reedyTargetArrow.map φ)
    change (T.reedyLatching).map φ ≫ T.inclusion.app (T.reedyTargetArrow.obj g) =
      T.inclusion.app (T.reedyTargetArrow.obj f) ≫
        T.middle.map (T.reedyTargetArrow.map φ) at hn
    rw [hn, ← Category.assoc]

/-- The actual factored cofibration arrow, functorially in original squares. -/
def reedyMiddle : Arrow (ExtensionCategory.Obj W) ⥤ ExtensionCategory.Obj W :=
  (ExtensionCategory.objects W).lift
    (ArrowDiagrams.toDiagramObj (Arrow.mk T.reedyMiddleInclusion)) (by
      intro f
      exact W.cof.comp_mem _ _
        (W.cof_pushout f.left.property (T.reedyLatching_isPushout f)) (T.cofibration _))

/-- The original square maps into its factorization by the actual first
factorization on its source and the relative pushout on its target. -/
def reedyInclusion : Arrow.leftFunc ⟶ T.reedyMiddle where
  app f := (ExtensionCategory.objects W).homMk
    (Arrow.homMk (T.inclusion.app ((reedySourceArrow (W := W)).obj f))
      (T.reedyLatchingLeft f ≫ T.inclusion.app (T.reedyTargetArrow.obj f)) (by
        change T.inclusion.app _ ≫ (T.reedyLatchingRight f ≫ _) =
          f.left.obj.hom ≫ (T.reedyLatchingLeft f ≫ _)
        rw [← Category.assoc, ← (T.reedyLatching_isPushout f).w, Category.assoc]))
  naturality f g φ := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact T.inclusion.naturality ((reedySourceArrow (W := W)).map φ)
    · change φ.left.hom.right ≫
          (T.reedyLatchingLeft g ≫ T.inclusion.app (T.reedyTargetArrow.obj g)) =
        (T.reedyLatchingLeft f ≫ T.inclusion.app (T.reedyTargetArrow.obj f)) ≫
          T.middle.map (T.reedyTargetArrow.map φ)
      rw [← Category.assoc, ← reedyLatchingLeft_naturality, Category.assoc]
      have hn := T.inclusion.naturality (T.reedyTargetArrow.map φ)
      change (T.reedyLatching).map φ ≫ T.inclusion.app (T.reedyTargetArrow.obj g) =
        T.inclusion.app (T.reedyTargetArrow.obj f) ≫
          T.middle.map (T.reedyTargetArrow.map φ) at hn
      rw [hn, ← Category.assoc]

/-- Both projection components are the original weak factorization projections. -/
def reedyProjection : T.reedyMiddle ⟶ Arrow.rightFunc where
  app f := (ExtensionCategory.objects W).homMk
    (Arrow.homMk (T.projection.app ((reedySourceArrow (W := W)).obj f))
      (T.projection.app (T.reedyTargetArrow.obj f)) (by
        change T.projection.app _ ≫ f.right.obj.hom =
          (T.reedyLatchingRight f ≫ T.inclusion.app (T.reedyTargetArrow.obj f)) ≫
            T.projection.app (T.reedyTargetArrow.obj f)
        rw [Category.assoc, T.factorization]
        exact (T.reedyLatchingRight_desc f).symm))
  naturality f g φ := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact T.projection.naturality ((reedySourceArrow (W := W)).map φ)
    · exact T.projection.naturality (T.reedyTargetArrow.map φ)

/-- The functorial Reedy factorization retains the original square strictly. -/
@[reassoc (attr := simp)]
theorem reedyInclusion_projection (f : Arrow (ExtensionCategory.Obj W)) :
    T.reedyInclusion.app f ≫ T.reedyProjection.app f = f.hom := by
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · exact T.factorization _
  · change (T.reedyLatchingLeft f ≫ T.inclusion.app (T.reedyTargetArrow.obj f)) ≫
      T.projection.app (T.reedyTargetArrow.obj f) = f.hom.hom.right
    rw [Category.assoc, T.factorization]
    exact T.reedyLatchingLeft_desc f

/-- The inclusion satisfies the actual joint relative-pushout cofibration test. -/
theorem reedyInclusion_cof (f : Arrow (ExtensionCategory.Obj W)) :
    ExtensionCategory.cof W (T.reedyInclusion.app f) :=
  ExtensionCategory.cof_of_relative W _ (T.cofibration _)
    (T.reedyLatching_isPushout f) (T.inclusion.app (T.reedyTargetArrow.obj f))
    rfl rfl (T.cofibration _)

/-- The projection is weak at both original vertices. -/
theorem reedyProjection_weak (f : Arrow (ExtensionCategory.Obj W)) :
    ExtensionCategory.weq W (T.reedyProjection.app f) := ⟨T.weak _, T.weak _⟩

/-- Genuine functorial factorizations transfer to the actual Reedy-arrow
Waldhausen structure. No functorial choices of App2 factorizations are made. -/
def reedyFactorization : FunctorialFactorization (ExtensionCategory.waldhausenStructure W) where
  middle := T.reedyMiddle
  inclusion := T.reedyInclusion
  projection := T.reedyProjection
  factorization := T.reedyInclusion_projection
  cofibration := T.reedyInclusion_cof
  weak := T.reedyProjection_weak

end Quillen.Waldhausen.FunctorialFactorization
