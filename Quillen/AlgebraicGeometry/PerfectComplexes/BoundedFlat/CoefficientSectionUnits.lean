/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitPullback
public import Quillen.CategoryTheory.Functor.IdentityAutomorphismNaturality
public import Quillen.CategoryTheory.Functor.IdentityAutomorphismEvaluation
public import Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.Units
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare

/-!
# Original units on the joint native coefficient sections

Faithful original evaluation lifts each actual geometric unit. Its genuine transition
isomorphism proves preservation by every joint reindexing map. Pulling a coefficient unit
along the original coefficient projection gives the same forward action after coefficient
change or scheme restriction. In particular the original Laurent coordinate is retained.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u v₁ v₂ v₃ w₁ w₂ w₃
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso

/-- The actual geometric unit lifted through the unchanged original evaluation equivalence. -/
def boundedFlatCoefficientSectionUnitIso (i : Index R) (r : (Γ(space i, ⊤))ˣ) :
    𝟭 (BoundedFlatCoefficientSections i) ≅ 𝟭 (BoundedFlatCoefficientSections i) :=
  lift (boundedFlatCoefficientOriginalEvaluation i) (boundedFlatPerfectGlobalUnitIso (space i) r)

private theorem coefficientSectionUnitIso_eq (i : Index R) (r : (Γ(space i, ⊤))ˣ) :
    boundedFlatCoefficientSectionUnitIso i r =
      lift (boundedFlatCoefficientOriginalEvaluation i)
        (boundedFlatPerfectGlobalUnitIso (space i) r) := rfl

/-- Original evaluation retains each prescribed forward unit component. -/
theorem boundedFlatCoefficientSectionUnitIso_evaluation_hom (i : Index R)
    (r : (Γ(space i, ⊤))ˣ) (S : BoundedFlatCoefficientSections i) :
    (boundedFlatCoefficientOriginalEvaluation i).map
        ((boundedFlatCoefficientSectionUnitIso i r).hom.app S) =
      (boundedFlatPerfectGlobalUnitIso (space i) r).hom.app
        ((boundedFlatCoefficientOriginalEvaluation i).obj S) := by
  rw [coefficientSectionUnitIso_eq]
  exact map_lift_hom (boundedFlatCoefficientOriginalEvaluation i)
    (boundedFlatPerfectGlobalUnitIso (space i) r) S

/-- Original evaluation also retains the inverse of that same unit. -/
theorem boundedFlatCoefficientSectionUnitIso_evaluation_inv (i : Index R)
    (r : (Γ(space i, ⊤))ˣ) (S : BoundedFlatCoefficientSections i) :
    (boundedFlatCoefficientOriginalEvaluation i).map
        ((boundedFlatCoefficientSectionUnitIso i r).inv.app S) =
      (boundedFlatPerfectGlobalUnitIso (space i) r).inv.app
        ((boundedFlatCoefficientOriginalEvaluation i).obj S) := by
  rw [coefficientSectionUnitIso_eq]
  exact map_lift_inv (boundedFlatCoefficientOriginalEvaluation i)
    (boundedFlatPerfectGlobalUnitIso (space i) r) S

private theorem preserves_of_evaluation_iso
    {C : Type v₁} [Category.{w₁} C] {D : Type v₂} [Category.{w₂} D]
    {E : Type v₃} [Category.{w₃} E] (F : C ⥤ D) (P : D ⥤ E) [P.Faithful]
    (Q : C ⥤ E) (e : F ⋙ P ≅ Q)
    (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) (γ : 𝟭 E ≅ 𝟭 E)
    (ha : Preserves Q α γ) (hb : Preserves P β γ) : Preserves F α β := by
  intro S
  apply P.map_injective
  exact (map_hom_eq_of_iso (F ⋙ P) Q e α γ ha S).trans (hb (F.obj S)).symm

/-- Every original joint reindexing preserves the original pulled-back forward unit. -/
theorem boundedFlatCoefficientSectionsMap_unit_preserves {i k : Index R} (f : i ⟶ k)
    (r : (Γ(space i, ⊤))ˣ) :
    Preserves (boundedFlatCoefficientSectionsMap f) (boundedFlatCoefficientSectionUnitIso i r)
      (boundedFlatCoefficientSectionUnitIso k
        (Units.map (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f).appTop.hom.toMonoidHom
          r)) := by
  apply preserves_of_evaluation_iso (boundedFlatCoefficientSectionsMap f)
    (boundedFlatCoefficientOriginalEvaluation k)
    (boundedFlatCoefficientOriginalEvaluation i ⋙
      boundedFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f))
    (boundedFlatCoefficientSectionReindexIso f) _ _
    (boundedFlatPerfectGlobalUnitIso (space k)
      (Units.map (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f).appTop.hom.toMonoidHom r))
  · intro S
    change (boundedFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)).map
      ((boundedFlatCoefficientOriginalEvaluation i).map
        ((boundedFlatCoefficientSectionUnitIso i r).hom.app S)) = _
    rw [boundedFlatCoefficientSectionUnitIso_evaluation_hom,
      boundedFlatPerfectPullback_map_globalUnit]
    rfl
  · exact boundedFlatCoefficientSectionUnitIso_evaluation_hom k _

/-- A coefficient unit pulled back along the actual native coefficient projection. -/
def boundedFlatCoefficientUnit (i : Index R) (r : (Γ(Spec i.2.right, ⊤))ˣ) :
    (Γ(space i, ⊤))ˣ :=
  Units.map (coefficientProjection i).appTop.hom.toMonoidHom r

/-- The original projection square preserves the exact coefficient-unit map. -/
theorem boundedFlatCoefficientUnit_map {i k : Index R} (f : i ⟶ k)
    (r : (Γ(Spec i.2.right, ⊤))ˣ) :
    Units.map (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f).appTop.hom.toMonoidHom
        (boundedFlatCoefficientUnit i r) =
      boundedFlatCoefficientUnit k
        (Units.map (Spec.map f.2.right).appTop.hom.toMonoidHom r) := by
  apply Units.ext
  have h := congrArg (fun g => g.appTop) (map_coefficientProjection f)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑r)

/-- The original ambient and restricted units agree through the actual native open map. -/
theorem boundedFlatCoefficientUnit_restriction {P Q : Over (Spec R)} (f : P ⟶ Q)
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Units.map (schemeMap f a).appTop.hom.toMonoidHom
        (boundedFlatCoefficientUnit (op Q, a) r) =
      boundedFlatCoefficientUnit (op P, a) r := by
  apply Units.ext
  have h := congrArg (fun g => g.appTop) (schemeMap_coefficientProjection f a)
  rw [Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑r)

/-- Every joint section map retains the same scalar after its actual coefficient map. -/
theorem boundedFlatCoefficientSectionsMap_coefficientUnit_preserves
    {i k : Index R} (f : i ⟶ k) (r : (Γ(Spec i.2.right, ⊤))ˣ) :
    Preserves (boundedFlatCoefficientSectionsMap f)
      (boundedFlatCoefficientSectionUnitIso i (boundedFlatCoefficientUnit i r))
      (boundedFlatCoefficientSectionUnitIso k (boundedFlatCoefficientUnit k
        (Units.map (Spec.map f.2.right).appTop.hom.toMonoidHom r))) := by
  rw [← boundedFlatCoefficientUnit_map f r]
  exact boundedFlatCoefficientSectionsMap_unit_preserves f (boundedFlatCoefficientUnit i r)

/-- Native scheme restriction keeps the unchanged forward coefficient unit. -/
theorem boundedFlatCoefficientSectionsRestriction_unit_preserves {P Q : Over (Spec R)}
    (f : P ⟶ Q) (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op P, a))
      (f.op, 𝟙 a))
      (boundedFlatCoefficientSectionUnitIso (op Q, a)
        (boundedFlatCoefficientUnit (op Q, a) r))
      (boundedFlatCoefficientSectionUnitIso (op P, a)
        (boundedFlatCoefficientUnit (op P, a) r)) := by
  have h := boundedFlatCoefficientSectionsMap_unit_preserves
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
    (boundedFlatCoefficientUnit (op Q, a) r)
  change Preserves _ _ (boundedFlatCoefficientSectionUnitIso (op P, a)
    (Units.map (schemeMap f a).appTop.hom.toMonoidHom
      (boundedFlatCoefficientUnit (op Q, a) r))) at h
  rw [boundedFlatCoefficientUnit_restriction] at h
  exact h

/-- The forward Laurent coordinate on the specified actual native coefficient fiber. -/
def boundedFlatCoefficientSectionLaurentUnitIso (P : Over (Spec R)) (a : Under R) :
    𝟭 (BoundedFlatCoefficientSections (op P, (laurentUnderFunctor R).obj a)) ≅
      𝟭 (BoundedFlatCoefficientSections (op P, (laurentUnderFunctor R).obj a)) :=
  boundedFlatCoefficientSectionUnitIso (op P, (laurentUnderFunctor R).obj a)
    (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a) (laurentGlobalUnit a.right))

/-- Coefficient change preserves the original forward Laurent coordinate on native sections. -/
theorem boundedFlatCoefficientSectionLaurentUnitIso_coefficient
    (P : Over (Spec R)) {a b : Under R} (g : a ⟶ b) :
    Preserves (boundedFlatCoefficientSectionsMap
      (i := (op P, (laurentUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj b)) (𝟙 (op P), (laurentUnderFunctor R).map g))
      (boundedFlatCoefficientSectionLaurentUnitIso P a)
      (boundedFlatCoefficientSectionLaurentUnitIso P b) := by
  have hr : Units.map (Spec.map ((laurentUnderFunctor R).map g).right).appTop.hom.toMonoidHom
      (laurentGlobalUnit a.right) = laurentGlobalUnit b.right :=
    laurentGlobalUnit_coefficient g.right
  unfold boundedFlatCoefficientSectionLaurentUnitIso
  simpa only [hr] using boundedFlatCoefficientSectionsMap_coefficientUnit_preserves
    (i := (op P, (laurentUnderFunctor R).obj a))
    (k := (op P, (laurentUnderFunctor R).obj b))
    (𝟙 (op P), (laurentUnderFunctor R).map g) (laurentGlobalUnit a.right)

/-- Scheme restriction preserves that same forward Laurent coordinate, without extra premises. -/
theorem boundedFlatCoefficientSectionLaurentUnitIso_restriction
    {P Q : Over (Spec R)} (f : P ⟶ Q) (a : Under R) :
    Preserves (boundedFlatCoefficientSectionsMap
      (i := (op Q, (laurentUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a)) (f.op, 𝟙 _))
      (boundedFlatCoefficientSectionLaurentUnitIso Q a)
      (boundedFlatCoefficientSectionLaurentUnitIso P a) :=
  boundedFlatCoefficientSectionsRestriction_unit_preserves f
    ((laurentUnderFunctor R).obj a) (laurentGlobalUnit a.right)

end Quillen.PerfectComplexes
