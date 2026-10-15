/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedBelowComparison
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlasqueExtensions
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GodementTotalExact
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GodementTotalQuasiIso

/-!
# The original lower-bounded flasque perfect model

This is the full subcategory of original locally perfect complexes of all module
sheaves that have a strict lower bound and flasque terms. The literal Godement
totalization lands in this subcategory and is Waldhausen-exact. Its original
augmentation supplies forward weak natural units on both original models.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.FlasqueBoundedBelow

/-- Original lower-bounded locally perfect complexes with every term flasque. -/
def objects (X : Scheme.{u}) : ObjectProperty (Complex X) := fun K =>
  BoundedBelow.objects X K ∧ ∀ n : ℤ, TopCat.Presheaf.IsFlasque (K.X n).presheaf

/-- All original chain maps between these complexes are retained. -/
abbrev Obj (X : Scheme.{u}) := (objects X).FullSubcategory

/-- Every actual zero complex belongs, including on the empty scheme. -/
lemma objects_of_isZero {X : Scheme.{u}} {K : Complex X} (hK : IsZero K) :
    objects X K := by
  refine ⟨BoundedBelow.objects_of_isZero hK, fun n => ?_⟩
  exact godement_isFlasque_of_isZero _
    ((HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).map_isZero hK)

instance containsZero (X : Scheme.{u}) : (objects X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, objects_of_isZero (isZero_zero _)⟩

/-- Membership is transported by the actual original complex isomorphism. -/
lemma objects_of_iso {X : Scheme.{u}} {K L : Complex X} (e : K ≅ L)
    (hK : objects X K) : objects X L := by
  refine ⟨BoundedBelow.objects_of_iso e hK.1, fun n => ?_⟩
  let : TopCat.Presheaf.IsFlasque
    ((HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).obj K).presheaf := hK.2 n
  exact flasque_of_iso ((HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).mapIso e)

instance isoClosed (X : Scheme.{u}) : (objects X).IsClosedUnderIsomorphisms where
  of_iso e := objects_of_iso e

/-- Actual extensions remain lower-bounded, locally perfect, and termwise flasque. -/
lemma objects_of_shortExact {X : Scheme.{u}} {S : ShortComplex (Complex X)}
    (hS : S.ShortExact) (h₁ : objects X S.X₁) (h₃ : objects X S.X₃) :
    objects X S.X₂ := by
  refine ⟨BoundedBelow.objects_of_shortExact hS h₁.1 h₃.1, fun n => ?_⟩
  let : TopCat.Presheaf.IsFlasque
    (S.map (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n)).X₁.presheaf := h₁.2 n
  let : TopCat.Presheaf.IsFlasque
    (S.map (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n)).X₃.presheaf := h₃.2 n
  exact flasque_of_shortExact_outer
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n)

instance extensionClosed (X : Scheme.{u}) :
    (abelianExactStructure (Complex X)).IsExtensionClosed (objects X) where
  prop_middle := objects_of_shortExact

instance closedUnderFiniteProducts (X : Scheme.{u}) :
    (objects X).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (Complex X)).extensionClosed_finiteProducts (objects X)

/-- The genuine full Waldhausen subcategory with inherited cofibrations and quasi-isomorphisms. -/
def waldhausen (X : Scheme.{u}) : Waldhausen.Structure (Obj X) :=
  Waldhausen.complexSubcategory (objects X)

/-- The literal full inclusion into the original lower-bounded perfect model. -/
def inclusion (X : Scheme.{u}) : Obj X ⥤ BoundedBelow.Obj X :=
  ObjectProperty.ιOfLE (fun _ h => h.1)

/-- The original inclusion is Waldhausen-exact. -/
lemma inclusion_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (waldhausen X).cof (waldhausen X).weq
    (BoundedBelow.waldhausen X).cof (BoundedBelow.waldhausen X).weq (inclusion X) :=
  Waldhausen.subcategoryInclusion_exact _ _ (fun _ h => h.1)

/-- Actual totalization has flasque terms, the same strict lower bound, and is locally perfect. -/
lemma godement_objects {X : Scheme.{u}} {K : Complex X}
    (hK : BoundedBelow.objects X K) : objects X ((godementTotal X).obj K) := by
  obtain ⟨hp, a, ha⟩ := hK
  let := ha
  let : QuasiIso ((godementTotalUnit X).app K) :=
    godementTotalUnit_quasiIso_of_isStrictlyGE X K a
  have hz : ∀ n, n < a → IsZero (K.X n) :=
    fun n hn => CochainComplex.isZero_of_isStrictlyGE K a n hn
  exact ⟨⟨(locallyPerfect_iff_of_quasiIso ((godementTotalUnit X).app K)).mp hp,
    a, godementTotal_isStrictlyGE K a hz⟩, godementTotal_isFlasque K a hz⟩

/-- The literal Godement total functor in the opposite direction. -/
def total (X : Scheme.{u}) : BoundedBelow.Obj X ⥤ Obj X :=
  ObjectProperty.lift _ ((BoundedBelow.objects X).ι ⋙ godementTotal X)
    (fun K => godement_objects K.property)

/-- The literal total preserves each specified strict lower bound. -/
lemma total_isStrictlyGE (X : Scheme.{u}) (K : BoundedBelow.Obj X) (a : ℤ)
    [K.obj.IsStrictlyGE a] : ((total X).obj K).obj.IsStrictlyGE a :=
  godementTotal_isStrictlyGE K.obj a
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)

instance total_additive (X : Scheme.{u}) : (total X).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (godementTotal X).map (f.hom + g.hom) =
      (godementTotal X).map f.hom + (godementTotal X).map g.hom
    exact CategoryTheory.Functor.map_add (godementTotal X)

/-- The original total functor preserves inherited actual short exact sequences. -/
def totalExactFunctor (X : Scheme.{u}) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex X)) (BoundedBelow.objects X))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex X)) (objects X)) where
  toFunctor := total X
  map_conflation S hS := by
    change (S.map (BoundedBelow.objects X).ι).ShortExact at hS
    change ((S.map (BoundedBelow.objects X).ι).map (godementTotal X)).ShortExact
    exact godementTotal_shortExact hS

/-- The original quotient-bearing cofibrations are preserved by actual exact totalization. -/
lemma total_cofibration {X : Scheme.{u}} {K L : BoundedBelow.Obj X} (f : K ⟶ L)
    (hf : (BoundedBelow.waldhausen X).cof f) : (waldhausen X).cof ((total X).map f) :=
  (totalExactFunctor X).map_inflation f hf

/-- Original weak arrows are preserved by the actual augmentation and two-out-of-three. -/
lemma total_weak {X : Scheme.{u}} {K L : BoundedBelow.Obj X} (f : K ⟶ L)
    (hf : (BoundedBelow.waldhausen X).weq f) : (waldhausen X).weq ((total X).map f) := by
  change QuasiIso f.hom at hf
  let fplus : (⟨K.obj, K.property.2⟩ : CochainComplex.Plus X.Modules) ⟶
    ⟨L.obj, L.property.2⟩ := ObjectProperty.homMk f.hom
  let : QuasiIso fplus.hom := hf
  change QuasiIso ((godementTotal X).map f.hom)
  exact godementTotalPlus_map_quasiIso fplus

/-- Actual totalization preserves zero, cofibrations, weak arrows, and their pushouts. -/
lemma total_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (BoundedBelow.waldhausen X).cof (BoundedBelow.waldhausen X).weq
    (waldhausen X).cof (waldhausen X).weq (total X) where
  zero h := (total X).map_isZero h
  cofibration f hf := total_cofibration f hf
  weak f hf := total_weak f hf
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (objects X).ι
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure (Complex X))
      (BoundedBelow.objects X) hi h).map (godementTotal X)

/-- The original augmentation lifted to the lower-bounded perfect source model. -/
def unit (X : Scheme.{u}) : 𝟭 (BoundedBelow.Obj X) ⟶ total X ⋙ inclusion X where
  app K := ObjectProperty.homMk ((godementTotalUnit X).app K.obj)
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (godementTotalUnit X).naturality f.hom

/-- Every component of the actual source unit is an original weak equivalence. -/
lemma unit_weak (X : Scheme.{u}) (K : BoundedBelow.Obj X) :
    (BoundedBelow.waldhausen X).weq ((unit X).app K) :=
  godementTotalUnit_quasiIso X ⟨K.obj, K.property.2⟩

/-- The same forward augmentation lifted to the full flasque source model. -/
def flasqueUnit (X : Scheme.{u}) : 𝟭 (Obj X) ⟶ inclusion X ⋙ total X where
  app K := ObjectProperty.homMk ((godementTotalUnit X).app K.obj)
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (godementTotalUnit X).naturality f.hom

/-- Every component of the actual flasque-source unit is an original weak equivalence. -/
lemma flasqueUnit_weak (X : Scheme.{u}) (K : Obj X) :
    (waldhausen X).weq ((flasqueUnit X).app K) :=
  godementTotalUnit_quasiIso X ⟨K.obj, K.property.1.2⟩

end Quillen.PerfectComplexes.FlasqueBoundedBelow

namespace Quillen.PerfectComplexes

/-- The full original lower-bounded, termwise-flasque locally perfect category. -/
abbrev FlasquePerfect (X : Scheme.{u}) := FlasqueBoundedBelow.Obj X

end Quillen.PerfectComplexes
