/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.ExactCategory.SFiltering
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Transfer
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# The underlying category of an exact quotient

For an exact structure `E` and a full subcategory specified by `A`, this file
constructs the category obtained by inverting the genuine weak isomorphisms of
`E` relative to `A`. Its strict universal property and functor-category universal
property are proved by the categorical localization construction in mathlib.

The construction needs no s-filtering assumption. Such hypotheses are needed to
construct the quotient's exact structure and prove exact localization, neither
of which is asserted or included as an axiom here.
-/
@[expose] public section


noncomputable section

universe v u v' u'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped ZeroObject

namespace Quillen

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- The underlying category of the exact quotient, constructed as the categorical
localization at finite composites of the two admissible generator classes.
An exact structure on this category is a separate theorem. -/
abbrev ExactQuotient (E : ExactStructure C) (A : ObjectProperty C) :=
  (E.weakIsomorphisms A).Localization

namespace ExactQuotient

variable (E : ExactStructure C) (A : ObjectProperty C)

/-- The quotient functor. -/
def Q : C ⥤ ExactQuotient E A := (E.weakIsomorphisms A).Q

instance : (Q E A).IsLocalization (E.weakIsomorphisms A) := by
  unfold Q
  infer_instance

/-- The categorical quotient has exactly the original objects, up to the
canonical equivalence of types. In particular there are no new object classes. -/
def objEquiv : C ≃ ExactQuotient E A :=
  Localization.Construction.objEquiv (E.weakIsomorphisms A)

@[simp]
lemma objEquiv_apply (X : C) : objEquiv E A X = (Q E A).obj X := rfl

lemma obj_surjective : Function.Surjective (Q E A).obj :=
  (objEquiv E A).surjective

instance : (Q E A).EssSurj := by
  unfold Q
  infer_instance

/-- Every weak isomorphism becomes invertible in the quotient. -/
lemma inverts : (E.weakIsomorphisms A).IsInvertedBy (Q E A) :=
  (E.weakIsomorphisms A).Q_inverts

lemma isIso_map_inflationWithCokernel {X Y : C} (i : X ⟶ Y)
    (hi : E.inflationWithCokernel A i) : IsIso ((Q E A).map i) :=
  inverts E A i (E.inflationWithCokernel_le_weakIsomorphisms A i hi)

lemma isIso_map_deflationWithKernel {X Y : C} (p : X ⟶ Y)
    (hp : E.deflationWithKernel A p) : IsIso ((Q E A).map p) :=
  inverts E A p (E.deflationWithKernel_le_weakIsomorphisms A p hp)

/-- The explicit isomorphism associated to a weak isomorphism. -/
def isoOfWeakIsomorphism {X Y : C} (f : X ⟶ Y) (hf : E.weakIsomorphisms A f) :
    (Q E A).obj X ≅ (Q E A).obj Y :=
  Localization.Construction.wIso f hf

@[simp]
lemma isoOfWeakIsomorphism_hom {X Y : C} (f : X ⟶ Y)
    (hf : E.weakIsomorphisms A f) :
    (isoOfWeakIsomorphism E A f hf).hom = (Q E A).map f := rfl

/-- The image of the first map of a conflation is invertible when the third
object is in the exact subcategory. -/
lemma isIso_map_f {S : ShortComplex C} (hS : E.conflation S) (hA : A S.X₃) :
    IsIso ((Q E A).map S.f) :=
  isIso_map_inflationWithCokernel E A S.f
    (E.inflationWithCokernel_of_conflation A hS hA)

/-- The dual inversion statement for a conflation's second map. -/
lemma isIso_map_g {S : ShortComplex C} (hS : E.conflation S) (hA : A S.X₁) :
    IsIso ((Q E A).map S.g) :=
  isIso_map_deflationWithKernel E A S.g
    (E.deflationWithKernel_of_conflation A hS hA)

variable {D : Type u'} [Category.{v'} D]

/-- The descent functor for any functor that inverts weak isomorphisms. -/
def lift (F : C ⥤ D) (hF : (E.weakIsomorphisms A).IsInvertedBy F) :
    ExactQuotient E A ⥤ D :=
  Localization.Construction.lift F hF

@[simp]
lemma Q_comp_lift (F : C ⥤ D) (hF : (E.weakIsomorphisms A).IsInvertedBy F) :
    Q E A ⋙ lift E A F hF = F :=
  Localization.Construction.fac F hF

/-- Strict uniqueness of descent. -/
lemma functor_ext (F G : ExactQuotient E A ⥤ D)
    (h : Q E A ⋙ F = Q E A ⋙ G) : F = G :=
  Localization.Construction.uniq F G h

/-- Existence and uniqueness of a factorization, rather than a universal
property assumed as part of a proposed quotient structure. -/
lemma existsUnique_lift (F : C ⥤ D) (hF : (E.weakIsomorphisms A).IsInvertedBy F) :
    ∃! G : ExactQuotient E A ⥤ D, Q E A ⋙ G = F := by
  refine ⟨lift E A F hF, Q_comp_lift E A F hF, ?_⟩
  intro G hG
  exact functor_ext E A G _ (hG.trans (Q_comp_lift E A F hF).symm)

/-- It suffices to specify inversion of the two elementary classes in order
to descend through the quotient. -/
def liftOfGenerators (F : C ⥤ D)
    (hi : (E.inflationWithCokernel A).IsInvertedBy F)
    (hp : (E.deflationWithKernel A).IsInvertedBy F) : ExactQuotient E A ⥤ D :=
  lift E A F ((E.weakIsomorphisms_isInvertedBy_iff A F).2 ⟨hi, hp⟩)

@[simp]
lemma Q_comp_liftOfGenerators (F : C ⥤ D)
    (hi : (E.inflationWithCokernel A).IsInvertedBy F)
    (hp : (E.deflationWithKernel A).IsInvertedBy F) :
    Q E A ⋙ liftOfGenerators E A F hi hp = F :=
  Q_comp_lift E A F _

/-- The strict universal property against every target category. -/
def strictUniversalProperty :
    Localization.StrictUniversalPropertyFixedTarget (Q E A) (E.weakIsomorphisms A) D :=
  Localization.strictUniversalPropertyFixedTargetQ _ D

/-- The full two-dimensional universal property, including natural
transformations between descended functors. -/
def functorEquivalence :
    (ExactQuotient E A ⥤ D) ≌ (E.weakIsomorphisms A).FunctorsInverting D :=
  Localization.Construction.whiskeringLeftEquivalence _ D

/-- A natural transformation descends from its restriction to the original
category. -/
def liftNatTrans {F G : ExactQuotient E A ⥤ D} (α : Q E A ⋙ F ⟶ Q E A ⋙ G) : F ⟶ G :=
  Localization.Construction.natTransExtension α

@[simp]
lemma whiskerLeft_liftNatTrans {F G : ExactQuotient E A ⥤ D}
    (α : Q E A ⋙ F ⟶ Q E A ⋙ G) :
    whiskerLeft (Q E A) (liftNatTrans E A α) = α :=
  Localization.Construction.whiskerLeft_natTransExtension α

/-- Enlarging the subcategory gives a canonical functor between the
underlying quotient categories. -/
def mapOfLE {B : ObjectProperty C} (hAB : A ≤ B) : ExactQuotient E A ⥤ ExactQuotient E B :=
  lift E A (Q E B) (fun _ _ f hf => inverts E B f (E.weakIsomorphisms_mono A hAB f hf))

@[simp]
lemma Q_comp_mapOfLE {B : ObjectProperty C} (hAB : A ≤ B) :
    Q E A ⋙ mapOfLE E A hAB = Q E B :=
  Q_comp_lift E A (Q E B) _

/-- Objects of the subcategory become isomorphic to the image of zero, even
before any additive or exact structure has been installed on the quotient. -/
def objIsoZero {X : C} (hX : A X) : (Q E A).obj X ≅ (Q E A).obj 0 :=
  isoOfWeakIsomorphism E A (0 : X ⟶ 0)
    (E.deflationWithKernel_le_weakIsomorphisms A _ (E.deflationWithKernel_to_zero A hX))

/-- Every quotient morphism has a right-fraction representative when the
subcategory is right filtering. -/
lemma exists_rightFraction (hA : E.RightFiltering A) {X Y : C}
    (f : (Q E A).obj X ⟶ (Q E A).obj Y) :
    ∃ (φ : (E.weakIsomorphisms A).RightFraction X Y), f = φ.map (Q E A) (inverts E A) := by
  let := hA.hasRightCalculusOfFractions E A
  exact Localization.exists_rightFraction (Q E A) (E.weakIsomorphisms A) f

/-- The dual fraction representation. -/
lemma exists_leftFraction (hA : E.LeftFiltering A) {X Y : C}
    (f : (Q E A).obj X ⟶ (Q E A).obj Y) :
    ∃ (φ : (E.weakIsomorphisms A).LeftFraction X Y), f = φ.map (Q E A) (inverts E A) := by
  let := hA.hasLeftCalculusOfFractions E A
  exact Localization.exists_leftFraction (Q E A) (E.weakIsomorphisms A) f

/-- Equality of images can be tested by precomposing with one actual weak
isomorphism in the ambient exact category. -/
lemma map_eq_iff_precomp (hA : E.RightFiltering A) {X Y : C} (f g : X ⟶ Y) :
    (Q E A).map f = (Q E A).map g ↔
      ∃ (T : C) (s : T ⟶ X) (_ : E.weakIsomorphisms A s), s ≫ f = s ≫ g := by
  let := hA.hasRightCalculusOfFractions E A
  exact MorphismProperty.map_eq_iff_precomp (Q E A) (E.weakIsomorphisms A) f g

/-- The dual test for equality of images. -/
lemma map_eq_iff_postcomp (hA : E.LeftFiltering A) {X Y : C} (f g : X ⟶ Y) :
    (Q E A).map f = (Q E A).map g ↔
      ∃ (T : C) (s : Y ⟶ T) (_ : E.weakIsomorphisms A s), f ≫ s = g ≫ s := by
  let := hA.hasLeftCalculusOfFractions E A
  exact MorphismProperty.map_eq_iff_postcomp (Q E A) (E.weakIsomorphisms A) f g

/-- Left filtering constructs the preadditive structure on the quotient;
this is an actual structure, independent of the future exactness theorem. -/
@[instance_reducible]
def leftPreadditive (hA : E.LeftFiltering A) : Preadditive (ExactQuotient E A) := by
  let := hA.hasLeftCalculusOfFractions E A
  exact Localization.preadditive (Q E A) (E.weakIsomorphisms A)

lemma leftQ_additive (hA : E.LeftFiltering A) :
    let := leftPreadditive E A hA
    (Q E A).Additive := by
  let := hA.hasLeftCalculusOfFractions E A
  exact Localization.functor_additive (Q E A) (E.weakIsomorphisms A)

/-- The left-filtering quotient is additive, with finite biproducts. -/
lemma leftHasFiniteBiproducts (hA : E.LeftFiltering A) :
    let := leftPreadditive E A hA
    HasFiniteBiproducts (ExactQuotient E A) := by
  let := leftPreadditive E A hA
  let := leftQ_additive E A hA
  let := (Q E A).hasFiniteProducts_of_additive_of_essSurj
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- Right filtering constructs a preadditive structure by applying the left
fraction construction to the opposite localization and transporting back. -/
@[instance_reducible]
def rightPreadditive (hA : E.RightFiltering A) : Preadditive (ExactQuotient E A) := by
  let := hA.hasRightCalculusOfFractions E A
  let : Preadditive (ExactQuotient E A)ᵒᵖ :=
    Localization.preadditive (Q E A).op (E.weakIsomorphisms A).op
  exact Preadditive.ofFullyFaithful (opOpEquivalence (ExactQuotient E A)).fullyFaithfulInverse

/-- The quotient functor is additive for the right-fraction construction. -/
lemma rightQ_additive (hA : E.RightFiltering A) :
    let := rightPreadditive E A hA
    (Q E A).Additive := by
  let := hA.hasRightCalculusOfFractions E A
  let : Preadditive (ExactQuotient E A)ᵒᵖ :=
    Localization.preadditive (Q E A).op (E.weakIsomorphisms A).op
  let : (Q E A).op.Additive :=
    Localization.functor_additive (Q E A).op (E.weakIsomorphisms A).op
  let := rightPreadditive E A hA
  let : (opOp (ExactQuotient E A)).Additive :=
    (opOpEquivalence (ExactQuotient E A)).fullyFaithfulInverse.additive_ofFullyFaithful
  let : (Q E A ⋙ opOp (ExactQuotient E A)).Additive := by
    let : (opOp C).Additive := ⟨by intros; rfl⟩
    change (opOp C ⋙ (Q E A).op.op).Additive
    infer_instance
  exact Functor.additive_of_comp_faithful (Q E A) (opOp (ExactQuotient E A))

/-- The right-filtering quotient has finite biproducts. -/
lemma rightHasFiniteBiproducts (hA : E.RightFiltering A) :
    let := rightPreadditive E A hA
    HasFiniteBiproducts (ExactQuotient E A) := by
  let := rightPreadditive E A hA
  let := rightQ_additive E A hA
  let := (Q E A).hasFiniteProducts_of_additive_of_essSurj
  exact HasFiniteBiproducts.of_hasFiniteProducts

end ExactQuotient
end Quillen
