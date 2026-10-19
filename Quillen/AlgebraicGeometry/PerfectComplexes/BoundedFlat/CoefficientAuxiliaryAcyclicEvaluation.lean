/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryEvaluationNull

/-!
# Actual acyclic evaluation with auxiliary support

The genuine native coarse-acyclic section evaluates to the geometric
coarse-acyclic bounded-flat complex. Both actual inclusions and flattening
to the original intersection support are retained. Exactness is proved for
the original fine structures, including the inverse native flattening.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

private theorem acyclic_evaluation_iff {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) (W : Structure D) (F : C ⥤ D)
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hw : ∀ {X Y} (p : X ⟶ Y), V.weq p ↔ W.weq (F.map p)) (X : C) :
    Acyclic V X ↔ Acyclic W (F.obj X) := by
  let hZ := hF.zero V.isZero
  have hp : F.map (V.isZero.to_ X) = hZ.to_ (F.obj X) := hZ.eq_of_src _ _
  change V.weq (V.isZero.to_ X) ↔ Acyclic W (F.obj X)
  rw [hw, hp]
  exact (acyclic_iff_weak_from_isZero W hZ _).symm

/-- Original coarse acyclicity is preserved and reflected by actual evaluation. -/
theorem boundedFlatCoefficientSupportedAcyclic_evaluation_iff (a : Under R)
    (S : BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    Acyclic (boundedFlatCoefficientSupportedOpenNested f T a).coarse S ↔
      Acyclic (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).coarse
        ((boundedFlatCoefficientSupportedEvaluation
          (boundedFlatCoefficientSupportOpen Q T a).ι).obj S) :=
  acyclic_evaluation_iff (boundedFlatCoefficientSupportedOpenWaldhausen f T a)
    (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a))
    (boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedOpenEvaluation_coarse_exact f T a)
    (fun p ↦ boundedFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a p) S

private theorem acyclic_lift_exact {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) {W : Structure D} (N : NestedWeakEquivalences W)
    (F : C ⥤ AcyclicCategory N)
    (h : IsExact V.cof V.weq W.cof W.weq (F ⋙ acyclicInclusion N)) :
    IsExact V.cof V.weq (acyclicStructure N).cof (acyclicStructure N).weq F where
  zero hZ := IsZero.of_full_of_faithful_of_isZero (acyclicObjects N).ι _ (h.zero hZ)
  cofibration p hp := h.cofibration p hp
  weak p hp := h.weak p hp
  pushout hi hp := IsPushout.of_map_of_faithful (acyclicObjects N).ι (h.pushout hi hp)

/-- Evaluate the original native acyclic section without replacing its complex. -/
def boundedFlatCoefficientSupportedAcyclicEvaluation (a : Under R) :
    AcyclicCategory (boundedFlatCoefficientSupportedOpenNested f T a) ⥤
      AcyclicCategory (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)) :=
  (acyclicObjects (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a))).lift
    (acyclicInclusion (boundedFlatCoefficientSupportedOpenNested f T a) ⋙
      boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientSupportOpen Q T a).ι)
    (fun S ↦ (boundedFlatCoefficientSupportedAcyclic_evaluation_iff f T a S.obj).mp S.property)

/-- Actual evaluation preserves the literal acyclic inclusion. -/
theorem boundedFlatCoefficientSupportedAcyclicEvaluation_inclusion (a : Under R) :
    boundedFlatCoefficientSupportedAcyclicEvaluation f T a ⋙
      acyclicInclusion (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)) =
      acyclicInclusion (boundedFlatCoefficientSupportedOpenNested f T a) ⋙
        boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientSupportOpen Q T a).ι :=
  Quillen.ObjectProperty.lift_comp_ι _ _ _

/-- Actual acyclic evaluation is exact for the original fine structures. -/
theorem boundedFlatCoefficientSupportedAcyclicEvaluation_exact (a : Under R) :
    IsExact (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).weq
      (acyclicStructure (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a))).cof
      (acyclicStructure (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a))).weq
      (boundedFlatCoefficientSupportedAcyclicEvaluation f T a) :=
  acyclic_lift_exact (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a))
    (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a))
    (boundedFlatCoefficientSupportedAcyclicEvaluation f T a)
    ((boundedFlatCoefficientSupportedAcyclicEvaluation_inclusion f T a).symm ▸
      (acyclicInclusion_exact (boundedFlatCoefficientSupportedOpenNested f T a)).comp
        (boundedFlatCoefficientSupportedEvaluation_exact
          (boundedFlatCoefficientSupportOpen Q T a).ι))

private theorem nestedEvaluation_flatten {C D : Type*} [Category* C] [Category* D]
    (P Q : ObjectProperty C) (R : ObjectProperty P.FullSubcategory)
    (A B : ObjectProperty D) (S : ObjectProperty A.FullSubcategory) (E : C ⥤ D)
    (hQ : ∀ X : R.FullSubcategory, Q X.obj.obj)
    (hA : ∀ X : P.FullSubcategory, A (E.obj X.obj))
    (hB : ∀ X : S.FullSubcategory, B X.obj.obj)
    (hBE : ∀ X : Q.FullSubcategory, B (E.obj X.obj))
    (hS : ∀ X : R.FullSubcategory, S ((A.lift (P.ι ⋙ E) hA).obj X.obj)) :
    ({ obj := fun X ↦ ⟨X.obj.obj, hQ X⟩
       map := fun p ↦ ObjectProperty.homMk p.hom.hom
       map_id := fun _ ↦ rfl
       map_comp := fun _ _ ↦ rfl } : R.FullSubcategory ⥤ Q.FullSubcategory) ⋙
      B.lift (Q.ι ⋙ E) hBE =
      S.lift (R.ι ⋙ A.lift (P.ι ⋙ E) hA) hS ⋙
      ({ obj := fun X ↦ ⟨X.obj.obj, hB X⟩
         map := fun p ↦ ObjectProperty.homMk p.hom.hom
         map_id := fun _ ↦ rfl
         map_comp := fun _ _ ↦ rfl } : S.FullSubcategory ⥤ B.FullSubcategory) := rfl

/-- Evaluation commutes with the actual flattening to intersection support. -/
theorem boundedFlatCoefficientSupportedAcyclicToFiber_evaluation (a : Under R) :
    boundedFlatCoefficientSupportedAcyclicToFiber f T a ⋙ boundedFlatCoefficientSupportedEvaluation
      (boundedFlatCoefficientFiberSupportOpen f T a).ι =
      boundedFlatCoefficientSupportedAcyclicEvaluation f T a ⋙
        boundedFlatPerfectSupportedOpenAcyclicToSupported
        (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a) := by
  unfold boundedFlatCoefficientSupportedAcyclicToFiber
    boundedFlatCoefficientSupportedAcyclicEvaluation
    boundedFlatPerfectSupportedOpenAcyclicToSupported
  unfold boundedFlatCoefficientSupportedEvaluation acyclicInclusion
  exact nestedEvaluation_flatten
    (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι)
    (acyclicObjects (boundedFlatCoefficientSupportedOpenNested f T a))
    (boundedFlatPerfectSupported (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatPerfectSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι)
    (acyclicObjects (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)))
    (boundedFlatCoefficientOriginalEvaluation (op Q, a) ⋙
      (boundedFlatPerfect (space (op Q, a))).ι)
    (fun X ↦ (boundedFlatCoefficientSupportedOpenAcyclic_iff f T a X.obj).mp X.property)
    (fun X ↦ ⟨((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj X.obj).property,
      X.property⟩)
    (fun X ↦ (boundedFlatPerfectSupported_sup_opensRange_iff (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a) X.obj.obj).mpr
      ⟨X.obj.property, (boundedFlatPerfectSupportedOpenAcyclic_iff (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) X.obj).mp X.property⟩)
    (fun X ↦ ⟨((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj X.obj).property,
      X.property⟩)
    (fun X ↦ by
      have h := (boundedFlatCoefficientSupportedAcyclic_evaluation_iff f T a X.obj).mp X.property
      unfold boundedFlatCoefficientSupportedEvaluation at h
      exact h)

/-- The actual evaluated native flattening is exact. -/
theorem boundedFlatCoefficientSupportedAcyclicToFiber_evaluation_exact (a : Under R) :
    IsExact (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).weq
      (boundedFlatPerfectSupportedWaldhausen
        (boundedFlatCoefficientFiberSupportOpen f T a).ι).cof
      (boundedFlatPerfectSupportedWaldhausen
        (boundedFlatCoefficientFiberSupportOpen f T a).ι).weq
      (boundedFlatCoefficientSupportedAcyclicToFiber f T a ⋙
        boundedFlatCoefficientSupportedEvaluation
        (boundedFlatCoefficientFiberSupportOpen f T a).ι) := by
  rw [boundedFlatCoefficientSupportedAcyclicToFiber_evaluation]
  exact (boundedFlatCoefficientSupportedAcyclicEvaluation_exact f T a).comp
    (boundedFlatPerfectSupportedOpenAcyclicToSupported_exact (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a))

private theorem supportedEvaluation_reflects_exact {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] {C : Type*} [Category* C]
    (V : Structure C) (I : C ⥤ BoundedFlatCoefficientSupportedSections j)
    (h : IsExact V.cof V.weq (boundedFlatPerfectSupportedWaldhausen j).cof
      (boundedFlatPerfectSupportedWaldhausen j).weq
      (I ⋙ boundedFlatCoefficientSupportedEvaluation j)) :
    IsExact V.cof V.weq (boundedFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen j).weq I := by
  let := boundedFlatCoefficientSupportedEvaluation_isEquivalence j
  exact {
    zero := fun hZ ↦ IsZero.of_full_of_faithful_of_isZero
      (boundedFlatCoefficientSupportedEvaluation j) _ (h.zero hZ)
    cofibration := fun p hp ↦
      (boundedFlatCoefficientSupportedSectionWaldhausen_cof_iff j _).mpr (h.cofibration p hp)
    weak := fun p hp ↦
      (boundedFlatCoefficientSupportedSectionWaldhausen_weq_iff j _).mpr (h.weak p hp)
    pushout := fun hi hp ↦ IsPushout.of_map_of_faithful
      (boundedFlatCoefficientSupportedEvaluation j) (h.pushout hi hp) }

/-- Native flattening to intersection support is exact for the original fine structures. -/
theorem boundedFlatCoefficientSupportedAcyclicToFiber_exact (a : Under R) :
    IsExact (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).weq
      (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.cof
      (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.weq
      (boundedFlatCoefficientSupportedAcyclicToFiber f T a) :=
  supportedEvaluation_reflects_exact (boundedFlatCoefficientFiberSupportOpen f T a).ι
    (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a))
    (boundedFlatCoefficientSupportedAcyclicToFiber f T a)
    (boundedFlatCoefficientSupportedAcyclicToFiber_evaluation_exact f T a)

/-- The original native flattening and its literal inverse induce all-degree K-equivalence. -/
def boundedFlatCoefficientSupportedAcyclicFiberKEquiv (a : Under R) (n : ℕ) :
    (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).K n ≃*
      (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.K n :=
  KEquivOfExactEquivalence _ _
    (boundedFlatCoefficientSupportedFiberAcyclicEquivalence f T a).symm
    (boundedFlatCoefficientSupportedAcyclicToFiber_exact f T a)
    (boundedFlatCoefficientSupportedFiberToAcyclic_exact f T a) n

/-- Native acyclic sections compute the original geometric intersection-support K-groups. -/
def boundedFlatCoefficientSupportedAcyclicSupportKEquiv (a : Under R) (n : ℕ) :
    (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).K n ≃*
      (boundedFlatPerfectSupportedWaldhausen
        (boundedFlatCoefficientFiberSupportOpen f T a).ι).K n :=
  (boundedFlatCoefficientSupportedAcyclicFiberKEquiv f T a n).trans
    (boundedFlatCoefficientSupportedSectionKEquiv
      (boundedFlatCoefficientFiberSupportOpen f T a).ι n)

end Quillen.PerfectComplexes
