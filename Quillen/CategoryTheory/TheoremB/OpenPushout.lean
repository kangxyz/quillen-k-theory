import Quillen.CategoryTheory.TheoremA.RealizationGluing
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-! Restriction of an actual topological pushout to an open subset of its
vertex is again an actual pushout. No injective attaching map is required. -/
noncomputable section
open CategoryTheory Limits
open scoped Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.OpenPushout
variable {A B C D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
  (sq : IsPushout i f g j) (U : Set D)

def source : TopCat.{u} := TopCat.of {a : A // g (i a) ∈ U}
def left : TopCat.{u} := TopCat.of {b : B // g b ∈ U}
def right : TopCat.{u} := TopCat.of {c : C // j c ∈ U}
def vertex : TopCat.{u} := TopCat.of U

def leftLeg : source (i := i) (g := g) U ⟶ left (g := g) U :=
  TopCat.ofHom ⟨fun a ↦ ⟨i a.1, a.2⟩, by fun_prop⟩

def rightLeg : source (i := i) (g := g) U ⟶ right (j := j) U :=
  TopCat.ofHom ⟨fun a ↦ ⟨f a.1, by
    change j (f a.1) ∈ U
    have hs : g (i a.1) = j (f a.1) := ConcreteCategory.congr_hom sq.w a.1
    exact hs ▸ a.2⟩, by fun_prop⟩

def leftInclusion : left (g := g) U ⟶ vertex U :=
  TopCat.ofHom ⟨fun b ↦ ⟨g b.1, b.2⟩, by fun_prop⟩

def rightInclusion : right (j := j) U ⟶ vertex U :=
  TopCat.ofHom ⟨fun c ↦ ⟨j c.1, c.2⟩, by fun_prop⟩

theorem square : leftLeg (i := i) (g := g) U ≫ leftInclusion (g := g) U =
    rightLeg sq U ≫ rightInclusion (j := j) U := by
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  exact ConcreteCategory.congr_hom sq.w a.1

section Desc
variable {Z : TopCat.{u}}
  (b : left (g := g) U ⟶ Z) (c : right (j := j) U ⟶ Z)
  (h : leftLeg (i := i) (g := g) U ≫ b = rightLeg sq U ≫ c)

private def leftOption : B → Option Z := by
  classical
  exact fun x ↦ if hx : g x ∈ U then some (b ⟨x, hx⟩) else none
private def rightOption : C → Option Z := by
  classical
  exact fun x ↦ if hx : j x ∈ U then some (c ⟨x, hx⟩) else none

include sq h in
private theorem option_square :
    (forget TopCat).map i ≫ (↾(leftOption U b) : (forget TopCat).obj B ⟶ Option Z) =
      (forget TopCat).map f ≫ (↾(rightOption U c) : (forget TopCat).obj C ⟶ Option Z) := by
  classical
  apply ConcreteCategory.hom_ext
  intro a
  change leftOption U b (i a) = rightOption U c (f a)
  have hs := ConcreteCategory.congr_hom sq.w a
  change g (i a) = j (f a) at hs
  by_cases ha : g (i a) ∈ U
  · have ha' : j (f a) ∈ U := hs ▸ ha
    simp only [leftOption, rightOption, CategoryTheory.types_comp_apply, dif_pos ha, dif_pos ha']
    exact congrArg some (ConcreteCategory.congr_hom h ⟨a, ha⟩)
  · have ha' : j (f a) ∉ U := hs ▸ ha
    simp [leftOption, rightOption, ha, ha']

private def optionDesc : D → Option Z :=
  (sq.map (forget TopCat)).desc (↾(leftOption U b)) (↾(rightOption U c)) (option_square sq U b c h)

private theorem optionDesc_left (x : B) : optionDesc sq U b c h (g x) = leftOption U b x :=
  ConcreteCategory.congr_hom ((sq.map (forget TopCat)).inl_desc _ _ _) x
private theorem optionDesc_right (x : C) : optionDesc sq U b c h (j x) = rightOption U c x :=
  ConcreteCategory.congr_hom ((sq.map (forget TopCat)).inr_desc _ _ _) x

private theorem optionDesc_some (x : U) : ∃ z : Z, optionDesc sq U b c h x = some z := by
  classical
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) x.1 with ⟨y, hy⟩ | ⟨y, hy⟩
  · change g y = x.1 at hy
    have hu : g y ∈ U := hy ▸ x.2
    refine ⟨b ⟨y, hu⟩, ?_⟩
    rw [← hy, optionDesc_left]
    simp [leftOption, hu]
  · change j y = x.1 at hy
    have hu : j y ∈ U := hy ▸ x.2
    refine ⟨c ⟨y, hu⟩, ?_⟩
    rw [← hy, optionDesc_right]
    simp [rightOption, hu]

def descFun : U → Z := fun x ↦ (optionDesc_some sq U b c h x).choose

theorem descFun_left (x : left (g := g) U) : descFun sq U b c h (leftInclusion U x) = b x := by
  classical
  have hs := (optionDesc_some sq U b c h (leftInclusion U x)).choose_spec
  change optionDesc sq U b c h (g x.1) = some (descFun sq U b c h (leftInclusion U x)) at hs
  rw [optionDesc_left] at hs
  simpa [leftOption, x.2] using hs.symm

theorem descFun_right (x : right (j := j) U) : descFun sq U b c h (rightInclusion U x) = c x := by
  classical
  have hs := (optionDesc_some sq U b c h (rightInclusion U x)).choose_spec
  change optionDesc sq U b c h (j x.1) = some (descFun sq U b c h (rightInclusion U x)) at hs
  rw [optionDesc_right] at hs
  simpa [rightOption, x.2] using hs.symm

theorem continuous_descFun (hU : IsOpen U) : Continuous (descFun sq U b c h) := by
  rw [continuous_def]
  intro W hW
  let V : Set D := (Subtype.val : U → D) '' ((descFun sq U b c h) ⁻¹' W)
  have hl : g ⁻¹' V = (Subtype.val : left (g := g) U → B) '' (b ⁻¹' W) := by
    ext x
    constructor
    · rintro ⟨z, hz, hzx⟩
      let xb : left (g := g) U := ⟨x, hzx ▸ z.2⟩
      refine ⟨xb, ?_, rfl⟩
      have he : leftInclusion U xb = z := Subtype.ext hzx.symm
      change b xb ∈ W
      rw [← descFun_left sq U b c h xb, he]
      exact hz
    · rintro ⟨xb, hxb, rfl⟩
      refine ⟨leftInclusion U xb, ?_, rfl⟩
      change descFun sq U b c h (leftInclusion U xb) ∈ W
      rw [descFun_left]
      exact hxb
  have hr : j ⁻¹' V = (Subtype.val : right (j := j) U → C) '' (c ⁻¹' W) := by
    ext x
    constructor
    · rintro ⟨z, hz, hzx⟩
      let xc : right (j := j) U := ⟨x, hzx ▸ z.2⟩
      refine ⟨xc, ?_, rfl⟩
      have he : rightInclusion U xc = z := Subtype.ext hzx.symm
      change c xc ∈ W
      rw [← descFun_right sq U b c h xc, he]
      exact hz
    · rintro ⟨xc, hxc, rfl⟩
      refine ⟨rightInclusion U xc, ?_, rfl⟩
      change descFun sq U b c h (rightInclusion U xc) ∈ W
      rw [descFun_right]
      exact hxc
  have hgl : IsOpen (g ⁻¹' V) := by
    rw [hl]
    exact (hU.preimage g.hom.continuous).isOpenEmbedding_subtypeVal.isOpenMap _
      (hW.preimage b.hom.continuous)
  have hjr : IsOpen (j ⁻¹' V) := by
    rw [hr]
    exact (hU.preimage j.hom.continuous).isOpenEmbedding_subtypeVal.isOpenMap _
      (hW.preimage c.hom.continuous)
  have hV : IsOpen V := by
    rw [TopCat.isOpen_iff_of_isColimit sq.cocone sq.isColimit]
    rintro (_ | _ | _)
    · change IsOpen (i ⁻¹' (g ⁻¹' V))
      exact hgl.preimage i.hom.continuous
    · exact hgl
    · exact hjr
  have hvpre : (Subtype.val : U → D) ⁻¹' V = (descFun sq U b c h) ⁻¹' W :=
    Set.preimage_image_eq _ Subtype.val_injective
  rw [← hvpre]
  exact hV.preimage continuous_subtype_val

/-- The continuous map descended from compatible maps on both restricted corners. -/
def desc (hU : IsOpen U) : vertex U ⟶ Z :=
  TopCat.ofHom ⟨descFun sq U b c h, continuous_descFun sq U b c h hU⟩

@[reassoc (attr := simp)] theorem left_desc (hU : IsOpen U) :
    leftInclusion (g := g) U ≫ desc sq U b c h hU = b := by
  apply ConcreteCategory.hom_ext
  exact descFun_left sq U b c h

@[reassoc (attr := simp)] theorem right_desc (hU : IsOpen U) :
    rightInclusion (j := j) U ≫ desc sq U b c h hU = c := by
  apply ConcreteCategory.hom_ext
  exact descFun_right sq U b c h

end Desc
end Quillen.OpenPushout

namespace Quillen.OpenPushout
variable {A B C D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
  (sq : IsPushout i f g j) (U : Set D)

include sq in
/-- The two restricted corner maps remain jointly determining. -/
theorem hom_ext {Z : TopCat.{u}} {m n : vertex U ⟶ Z}
    (hl : leftInclusion (g := g) U ≫ m = leftInclusion U ≫ n)
    (hr : rightInclusion (j := j) U ≫ m = rightInclusion U ≫ n) : m = n := by
  apply ConcreteCategory.hom_ext
  intro x
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) x.1 with ⟨y, hy⟩ | ⟨y, hy⟩
  · change g y = x.1 at hy
    let y' : left (g := g) U := ⟨y, hy ▸ x.2⟩
    have he : leftInclusion U y' = x := Subtype.ext hy
    rw [← he]
    exact ConcreteCategory.congr_hom hl y'
  · change j y = x.1 at hy
    let y' : right (j := j) U := ⟨y, hy ▸ x.2⟩
    have he : rightInclusion U y' = x := Subtype.ext hy
    rw [← he]
    exact ConcreteCategory.congr_hom hr y'

/-- The actual cocone obtained by restricting every corner to an open
subset of the original pushout vertex is colimiting. -/
def restrictedIsColimit (hU : IsOpen U) :
    IsColimit (PushoutCocone.mk (leftInclusion (g := g) U) (rightInclusion (j := j) U)
      (square sq U)) :=
  PushoutCocone.IsColimit.mk _
    (fun s ↦ desc sq U s.inl s.inr s.condition hU)
    (fun s ↦ left_desc sq U s.inl s.inr s.condition hU)
    (fun s ↦ right_desc sq U s.inl s.inr s.condition hU)
    (fun s m hm₁ hm₂ ↦ hom_ext sq U
      (hm₁.trans (left_desc sq U s.inl s.inr s.condition hU).symm)
      (hm₂.trans (right_desc sq U s.inl s.inr s.condition hU).symm))

/-- Open restriction preserves every topological pushout, without an
injectivity or closed-embedding assumption on either attaching map. -/
theorem isPushout (hU : IsOpen U) :
    IsPushout (leftLeg (i := i) (g := g) U) (rightLeg sq U)
      (leftInclusion (g := g) U) (rightInclusion (j := j) U) :=
  IsPushout.of_isColimit (restrictedIsColimit sq U hU)

end Quillen.OpenPushout
