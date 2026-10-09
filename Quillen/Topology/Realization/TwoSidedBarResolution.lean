import Quillen.Topology.Realization.TwoSidedBarEvaluation
import Quillen.Topology.ClassifyingSpace.Equivalence

/-! # The elementary resolution category in each transposed bar row

An object consists of an original outer ordinal, an inner simplex at that
ordinal, and an arrow to the fixed inner ordinal. Evaluation sends it to the
transported simplex. Each evaluation fiber has its genuine terminal object.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u

namespace Quillen.TwoSidedBar
variable (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (q : SimplexCategoryᵒᵖ)

/-- An actual simplex with an arrow to the evaluation ordinal. -/
structure Resolution where
  index : Index.{u}
  value : (H.obj (indexProjection.obj index)).obj q
  arrow : indexProjection.obj index ⟶ q

namespace Resolution
variable {H q}

@[ext] theorem ext {a b : Resolution H q} (h : a.index = b.index)
    (hv : HEq a.value b.value) (ha : HEq a.arrow b.arrow) : a = b := by
  cases a; cases b; cases h; cases hv; cases ha; rfl

/-- A genuine transport map respecting both the simplex and the terminal arrow. -/
structure Hom (a b : Resolution H q) where
  map : a.index ⟶ b.index
  value : (H.map (indexProjection.map map)).app q a.value = b.value
  arrow : indexProjection.map map ≫ b.arrow = a.arrow

@[ext] theorem Hom.ext {a b : Resolution H q} {f g : Hom a b} (h : f.map = g.map) : f = g := by
  cases f; cases g; cases h; rfl

instance : SmallCategory (Resolution H q) where
  Hom := Hom
  id a := {
    map := 𝟙 a.index
    value := by
      change (H.map (𝟙 _)).app q a.value = a.value
      rw [H.map_id]
      rfl
    arrow := by
      change (𝟙 _) ≫ a.arrow = a.arrow
      exact Category.id_comp _ }
  comp f g := {
    map := f.map ≫ g.map
    value := by
      simp only [Functor.map_comp, NatTrans.comp_app, types_comp_apply]
      rw [f.value, g.value]
    arrow := by rw [Functor.map_comp, Category.assoc, g.arrow, f.arrow] }
  id_comp f := by apply Hom.ext; exact Category.id_comp _
  comp_id f := by apply Hom.ext; exact Category.comp_id _
  assoc f g h := by apply Hom.ext; exact Category.assoc _ _ _

variable (H q)

/-- Forgetting the coefficient and augmentation arrow. -/
def forget : Resolution H q ⥤ Index.{u} where
  obj a := a.index
  map f := f.map

/-- Evaluation lands in the discrete set of original diagonal simplices. -/
def evaluate : Resolution H q ⥤ Discrete ((H.obj q).obj q) where
  obj a := ⟨(H.map a.arrow).app q a.value⟩
  map {a b} f := Discrete.eqToHom (by
    change (H.map a.arrow).app q a.value = (H.map b.arrow).app q b.value
    rw [← f.arrow, H.map_comp]
    change (H.map b.arrow).app q ((H.map (indexProjection.map f.map)).app q a.value) = _
    rw [f.value])

/-- The actual terminal object in each evaluation fiber. -/
def sectionFunctor : Discrete ((H.obj q).obj q) ⥤ Resolution H q where
  obj a := ⟨AsSmall.up.obj q, a.as, 𝟙 q⟩
  map {a b} f := {
    map := 𝟙 _
    value := by
      change (H.map (𝟙 q)).app q a.as = b.as
      rw [H.map_id]
      exact Discrete.eq_of_hom f
    arrow := by
      change (𝟙 q) ≫ (𝟙 q) = 𝟙 q
      exact Category.id_comp _ }
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by
    apply Hom.ext
    change (𝟙 (AsSmall.up.obj q)) = 𝟙 _ ≫ 𝟙 _
    simp

/-- The literal augmentation arrow contracts each evaluation fiber to its
terminal object, with no choice of paths or inverse families. -/
def contraction : 𝟭 (Resolution H q) ⟶ evaluate H q ⋙ sectionFunctor H q where
  app a := {
    map := AsSmall.up.map a.arrow
    value := rfl
    arrow := Category.comp_id _ }
  naturality a b f := by
    apply Hom.ext
    change f.map ≫ AsSmall.up.map b.arrow = AsSmall.up.map a.arrow ≫ 𝟙 _
    apply ULift.ext
    change indexProjection.map f.map ≫ b.arrow = a.arrow ≫ 𝟙 q
    simpa using f.arrow

/-- Evaluation followed by the terminal section is exactly identity on the
discrete original simplex set. -/
def sectionEvaluationIso : sectionFunctor H q ⋙ evaluate H q ≅ 𝟭 _ :=
  NatIso.ofComponents (fun a ↦ eqToIso (by
    apply Discrete.ext
    change (H.map (𝟙 q)).app q a.as = a.as
    rw [H.map_id]
    rfl))

end Resolution
end Quillen.TwoSidedBar
