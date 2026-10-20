/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCarrier
/-! Two pushout descents extending a compatible Laurent map and cylinder. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenFold
open CutOpenCarrier
private theorem realized_left {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z) (y : |Y|) :
    SSet.toTop.map ((coprod.inl : Y ⟶ Y ⨿ Z) ≫ DoubleCylinder.simplicialEnds f g) y =
      DoubleCylinder.realizedEnds f g (Sum.inl y) := by
  have h : SSet.toTop.map ((coprod.inl : Y ⟶ Y ⨿ Z) ≫ DoubleCylinder.simplicialEnds f g) =
      (TopCat.binaryCofan |Y| |Z|).inl ≫ DoubleCylinder.realizedEnds f g := by
    simpa only [Functor.map_comp, DoubleCylinder.realizedEnds, Category.assoc,
      Iso.hom_inv_id_assoc] using congrArg
      (fun k ↦ k ≫ (realizationBinarySumIso Y Z).inv ≫
        SSet.toTop.map (DoubleCylinder.simplicialEnds f g))
      (realizationBinarySumIso_inl Y Z)
  exact ConcreteCategory.congr_hom h y
variable {V W T : Model.{u}} (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (ε : G.functor ≅ (F ≫ J).functor) (Q : TopCat.{u})
  (l : C(|parameterSSet G|, Q)) (c : C(|parameterSSet F| × unitInterval, Q)) (q : Q)
  (h0 : ∀ z, c (z, 0) = l (mapParameter (attachPostcompNode F J G ε) z))
  (h1 : ∀ z, c (z, 1) = q)

/-- Cylinder Map for the exact original reference and parameter data. -/
def cylinderMap : TopCat.of (|parameterSSet F| × TopCat.I.{u}) ⟶ Q :=
  TopCat.ofHom ⟨fun z ↦ c (z.1, z.2.down), by fun_prop⟩
/-- First Ends for the exact original reference and parameter data. -/
def firstEnds : TopCat.of (|parameterSSet G| ⊕ |tipSSet.{u}|) ⟶ Q :=
  TopCat.ofHom ⟨Sum.elim l (fun _ ↦ q), continuous_sum_dom.mpr ⟨l.continuous, continuous_const⟩⟩
include h0 h1 in
/-- First square for the exact original reference and parameter data. -/
theorem first_square : intervalEndpoints |parameterSSet F| ≫ cylinderMap F Q c =
    DoubleCylinder.endMap (SSet.toTop.map (attaching F J G ε)) (SSet.toTop.map (erase F)) ≫
      firstEnds G Q l q := by
  ext z
  cases z with
  | inl z => exact h0 z
  | inr z => exact h1 z
/-- First Map for the exact original reference and parameter data. -/
def firstMap : |firstSimplicial F J G ε| ⟶ Q :=
  (first_isPushout F J G ε).desc (cylinderMap F Q c) (firstEnds G Q l q)
    (first_square F J G ε Q l c q h0 h1)
/-- First left for the exact original reference and parameter data. -/
theorem first_left (z : |parameterSSet G|) :
    firstMap F J G ε Q l c q h0 h1 (SSet.toTop.map (left₀ F J G ε) z) = l z := by
  exact (congrArg (firstMap F J G ε Q l c q h0 h1)
    (realized_left (attaching F J G ε) (erase F) z)).trans
      (ConcreteCategory.congr_hom ((first_isPushout F J G ε).inr_desc _ _ _) (Sum.inl z))
/-- First cylinder for the exact original reference and parameter data. -/
theorem first_cylinder (z : |parameterSSet F|) (s : unitInterval) :
    firstMap F J G ε Q l c q h0 h1
      (DoubleCylinder.realizedCylinder (attaching F J G ε) (erase F) (z, ULift.up s)) = c (z, s) :=
  ConcreteCategory.congr_hom ((first_isPushout F J G ε).inl_desc _ _ _) (z, ULift.up s)
/-- Second Ends for the exact original reference and parameter data. -/
def secondEnds : TopCat.of (|firstSimplicial F J G ε| ⊕ |tipSSet.{u}|) ⟶ Q :=
  TopCat.ofHom ⟨Sum.elim (firstMap F J G ε Q l c q h0 h1) (fun _ ↦ q),
    continuous_sum_dom.mpr ⟨(firstMap F J G ε Q l c q h0 h1).hom.continuous, continuous_const⟩⟩
/-- Second square for the exact original reference and parameter data. -/
theorem second_square : intervalEndpoints |parameterSSet F| ≫ cylinderMap F Q c =
    DoubleCylinder.endMap (SSet.toTop.map (secondAttaching F J G ε ε)) (SSet.toTop.map (erase F)) ≫
      secondEnds F J G ε Q l c q h0 h1 := by
  ext z
  cases z with
  | inl z =>
    change c (z, 0) = firstMap F J G ε Q l c q h0 h1
      (SSet.toTop.map (secondAttaching F J G ε ε) z)
    rw [secondAttaching, Functor.map_comp]
    exact (h0 z).trans (first_left F J G ε Q l c q h0 h1 _).symm
  | inr z => exact h1 z
/-- Map for the exact original reference and parameter data. -/
def map : C(space F J G ε ε, Q) :=
  ((second_isPushout F J G ε ε).desc (cylinderMap F Q c)
    (secondEnds F J G ε Q l c q h0 h1)
    (second_square F J G ε Q l c q h0 h1)).hom
/-- Map first for the exact original reference and parameter data. -/
theorem map_first (z : |firstSimplicial F J G ε|) :
    map F J G ε Q l c q h0 h1 (SSet.toTop.map (left₁ F J G ε ε) z) =
      firstMap F J G ε Q l c q h0 h1 z := by
  exact (congrArg (map F J G ε Q l c q h0 h1)
    (realized_left (secondAttaching F J G ε ε) (erase F) z)).trans
      (ConcreteCategory.congr_hom ((second_isPushout F J G ε ε).inr_desc _ _ _) (Sum.inl z))
/-- Map laurent for the exact original reference and parameter data. -/
theorem map_laurent (z : |parameterSSet G|) :
    map F J G ε Q l c q h0 h1 (laurentInclusion F J G ε ε z) = l z := by
  change map F J G ε Q l c q h0 h1 (SSet.toTop.map (left₁ F J G ε ε) _) = _
  rw [map_first, first_left]
/-- Map cylinder for the exact original reference and parameter data. -/
theorem map_cylinder (z : |parameterSSet F|) (s : unitInterval) :
    map F J G ε Q l c q h0 h1 (cylinderMinus F J G ε ε (z, s)) = c (z, s) := by
  change map F J G ε Q l c q h0 h1 (SSet.toTop.map (left₁ F J G ε ε) _) = _
  rw [map_first, first_cylinder]
end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenFold
