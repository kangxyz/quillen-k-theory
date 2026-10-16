/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Diamond
public import Aglib.CategoryTheory.Abelian.Subcategory.Exact
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Devissage.Setup
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Filtration sums for algebraic dévissage

The inclusion of a full abelian subcategory closed under subobjects, quotients,
finite products and zero induces an isomorphism on algebraic Grothendieck groups
when every ambient object admits a finite filtration with factors in it.

The proof constructs pullback intersections. A double-cokernel isomorphism gives
the diamond identity inside the smaller Grothendieck group, and induction proves
that filtration sums are independent of filtration. A second pullback induction
proves additivity on arbitrary short exact sequences, yielding the inverse map.
No extension closure or finite-length hypothesis is used. This is the algebraic
theorem, not a comparison with homotopical Quillen `K₀` or higher dévissage.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CategoryTheory.ObjectProperty



noncomputable section
universe v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]
  (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts]

/-- The class of an ambient object known to lie in the smaller category. -/
def factorClass (X : C) (hX : P X) : (subcategoryExactStructure P).GrothendieckGroup :=
  (subcategoryExactStructure P).grothendieckClass ⟨X, hX⟩

lemma factorClass_iso {X Y : C} (e : X ≅ Y) (hX : P X) (hY : P Y) :
    factorClass P X hX = factorClass P Y hY :=
  (subcategoryExactStructure P).grothendieckClass_iso (P.isoMk e)

lemma factorClass_zero {X : C} (hX : IsZero X) (hP : P X) : factorClass P X hP = 0 := by
  apply (subcategoryExactStructure P).grothendieckClass_of_isZero
  rw [IsZero.iff_id_eq_zero]
  ext
  exact hX.eq_of_src _ _

/-- Short exact sequences all of whose objects satisfy `P` give relations
inside the smaller Grothendieck group. -/
lemma factorClass_additive (S : ShortComplex C) (hS : S.ShortExact)
    (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) :
    factorClass P S.X₂ h₂ = factorClass P S.X₁ h₁ + factorClass P S.X₃ h₃ := by
  let T : ShortComplex P.FullSubcategory :=
    ShortComplex.mk (P.homMk S.f : ⟨S.X₁, h₁⟩ ⟶ ⟨S.X₂, h₂⟩)
      (P.homMk S.g : ⟨S.X₂, h₂⟩ ⟶ ⟨S.X₃, h₃⟩) (by ext; exact S.zero)
  have hT : T.ShortExact := CategoryTheory.ShortExact.reflects_shortExact_of_faithful P.ι hS
  exact (subcategoryExactStructure P).grothendieckClass_additive hT

/-- The sum of the successive factor classes, in the smaller Grothendieck group. -/
def filtrationSum {X : C} : (abelianExactStructure C).Filtration P X →
    (subcategoryExactStructure P).GrothendieckGroup
  | .zero _ => 0
  | .step S _ F hP => filtrationSum F + factorClass P S.X₃ hP

@[simp] lemma filtrationSum_zero {X : C} (hX : IsZero X) :
    filtrationSum P (.zero hX) = 0 := rfl

@[simp] lemma filtrationSum_step (S : ShortComplex C) (hS : S.ShortExact)
    (F : (abelianExactStructure C).Filtration P S.X₁) (hP : P S.X₃) :
    filtrationSum P (.step S hS F hP) = filtrationSum P F + factorClass P S.X₃ hP := rfl

/-- If the endpoint itself satisfies `P`, the sum already telescopes entirely
inside the smaller category. -/
lemma filtrationSum_of_mem {X : C} (F : (abelianExactStructure C).Filtration P X)
    (hX : P X) : filtrationSum P F = factorClass P X hX := by
  induction F with
  | zero h => exact (factorClass_zero P h hX).symm
  | step S hS F hP ih =>
    have hS' : S.ShortExact := hS
    let := hS'.mono_f
    have h₁ := P.prop_of_mono S.f hX
    change filtrationSum P F + factorClass P S.X₃ hP = _
    rw [ih h₁]
    exact (factorClass_additive P S hS h₁ hX hP).symm

/-- The diamond relation between the four quotient factors of an intersection
square. It is a relation in the *smaller* Grothendieck group. -/
lemma pullback_factorClass_identity {I U A X : C} {t : I ⟶ U} {l : I ⟶ A}
    {r : U ⟶ X} {b : A ⟶ X} (sq : IsPullback t l r b)
    (hV : P (cokernel r)) (hB : P (cokernel b)) :
    factorClass P (cokernel t) (pullback_cokernel_mem P sq hB) +
        factorClass P (cokernel r) hV =
      factorClass P (cokernel l) (pullback_cokernel_mem P sq.flip hV) +
        factorClass P (cokernel b) hB := by
  let m₁ := cokernel.map t b l r sq.w
  let m₂ := cokernel.map l r t b sq.w.symm
  let := Abelian.mono_cokernel_map_of_isPullback sq
  let := Abelian.mono_cokernel_map_of_isPullback sq.flip
  have h₁ := P.prop_of_epi (cokernel.π m₁) hB
  have h₂ := P.prop_of_epi (cokernel.π m₂) hV
  have eq₁ := factorClass_additive P
    (ShortComplex.mk m₁ (cokernel.π m₁) (cokernel.condition m₁))
    { exact := ShortComplex.cokernelSequence_exact m₁ }
    (pullback_cokernel_mem P sq hB) hB h₁
  have eq₂ := factorClass_additive P
    (ShortComplex.mk m₂ (cokernel.π m₂) (cokernel.condition m₂))
    { exact := ShortComplex.cokernelSequence_exact m₂ }
    (pullback_cokernel_mem P sq.flip hV) hV h₂
  have eq₃ := factorClass_iso P (doubleCokernelSwap t l r b sq.w) h₁ h₂
  dsimp only [ShortComplex.mk] at eq₁ eq₂
  rw [eq₁, eq₂, eq₃]
  abel

/-- Restrict a finite filtration to a subobject whose complementary quotient
lies in `P`. The resulting filtration sum satisfies the expected subtraction
formula. This constructs the intersections, rather than postulating a common
refinement or using a finite-length hypothesis. -/
theorem exists_restricted_filtration {X : C}
    (F : (abelianExactStructure C).Filtration P X) {A : C}
    (i : A ⟶ X) [Mono i] (hB : P (cokernel i)) :
    ∃ G : (abelianExactStructure C).Filtration P A,
      filtrationSum P F = filtrationSum P G + factorClass P (cokernel i) hB := by
  induction F generalizing A with
  | zero hX =>
    have hA := IsZero.of_mono i hX
    refine ⟨.zero hA, ?_⟩
    have hQ := IsZero.of_epi (cokernel.π i) hX
    simp [factorClass_zero P hQ hB]
  | step S hS F hP ih =>
    have hS' : S.ShortExact := hS
    let := hS'.mono_f
    let e : cokernel S.f ≅ S.X₃ :=
      (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS'.gIsCokernel
    have hV : P (cokernel S.f) := P.prop_of_iso e.symm hP
    let sq := IsPullback.of_hasPullback S.f i
    have ht := pullback_cokernel_mem P sq hB
    have hl := pullback_cokernel_mem P sq.flip hV
    obtain ⟨G, hG⟩ := ih (pullback.fst S.f i) ht
    let T := ShortComplex.mk (pullback.snd S.f i)
      (cokernel.π (pullback.snd S.f i)) (cokernel.condition _)
    have hT : T.ShortExact := { exact := ShortComplex.cokernelSequence_exact _ }
    refine ⟨.step T hT G hl, ?_⟩
    change filtrationSum P F + factorClass P S.X₃ hP =
      (filtrationSum P G + factorClass P (cokernel (pullback.snd S.f i)) hl) +
        factorClass P (cokernel i) hB
    rw [hG, ← factorClass_iso P e hV hP, add_assoc,
      pullback_factorClass_identity P sq hV hB, ← add_assoc]

/-- The finite-filtration sum in `G(P)` is independent of every choice of
filtration. Intersections furnish the induction step, so the theorem does not
assume composition series or finite length. -/
theorem filtrationSum_eq {X : C}
    (F G : (abelianExactStructure C).Filtration P X) :
    filtrationSum P F = filtrationSum P G := by
  induction F with
  | zero hX =>
    rw [filtrationSum_zero, filtrationSum_of_mem P G (P.prop_of_isZero hX),
      factorClass_zero P hX]
  | step S hS F hP ih =>
    have hS' : S.ShortExact := hS
    let := hS'.mono_f
    let e : cokernel S.f ≅ S.X₃ :=
      (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS'.gIsCokernel
    have hV : P (cokernel S.f) := P.prop_of_iso e.symm hP
    obtain ⟨H, hH⟩ := exists_restricted_filtration P G S.f hV
    change filtrationSum P F + factorClass P S.X₃ hP = _
    rw [hH, ih H, factorClass_iso P e hV hP]

/-- The well-defined object invariant furnished by finite filtrations. -/
def inverseObjClass (h : FiltrationHypothesis P) (X : C) :
    (subcategoryExactStructure P).GrothendieckGroup :=
  filtrationSum P (Classical.choice (h X))

lemma inverseObjClass_eq_sum (h : FiltrationHypothesis P) {X : C}
    (F : (abelianExactStructure C).Filtration P X) :
    inverseObjClass P h X = filtrationSum P F :=
  filtrationSum_eq P _ F

lemma inverseObjClass_of_mem (h : FiltrationHypothesis P) {X : C} (hX : P X) :
    inverseObjClass P h X = factorClass P X hX :=
  filtrationSum_of_mem P _ hX

lemma inverseObjClass_of_isZero (h : FiltrationHypothesis P) {X : C} (hX : IsZero X) :
    inverseObjClass P h X = 0 := by
  rw [inverseObjClass_of_mem P h (P.prop_of_isZero hX), factorClass_zero P hX]

/-- Additivity when the complementary quotient lies in the smaller category. -/
lemma inverseObjClass_mono (h : FiltrationHypothesis P) {A X : C}
    (i : A ⟶ X) [Mono i] (hB : P (cokernel i)) :
    inverseObjClass P h X = inverseObjClass P h A + factorClass P (cokernel i) hB := by
  obtain ⟨G, hG⟩ := exists_restricted_filtration P (Classical.choice (h X)) i hB
  exact hG.trans (congrArg (· + factorClass P (cokernel i) hB)
    (inverseObjClass_eq_sum P h G).symm)

lemma inverseObjClass_iso (h : FiltrationHypothesis P) {X Y : C} (e : X ≅ Y) :
    inverseObjClass P h X = inverseObjClass P h Y := by
  have hz := isZero_cokernel_of_epi e.hom
  rw [inverseObjClass_mono P h e.hom (P.prop_of_isZero hz),
    factorClass_zero P hz, add_zero]

/-- Additivity across an epimorphism, proved by induction on an actual
finite filtration of its target. Pullbacks identify the two kernels and the
successive complementary quotients. -/
lemma inverseObjClass_epi_filtration (h : FiltrationHypothesis P) {B : C}
    (F : (abelianExactStructure C).Filtration P B) {X : C}
    (p : X ⟶ B) [Epi p] :
    inverseObjClass P h X = inverseObjClass P h (kernel p) + filtrationSum P F := by
  induction F generalizing X with
  | zero hB =>
    let e : kernel p ≅ X := kernelIsoOfEq (hB.eq_of_tgt p 0) ≪≫ kernelZeroIsoSource
    simpa using (inverseObjClass_iso P h e).symm
  | step S hS F hP ih =>
    have hS' : S.ShortExact := hS
    let := hS'.mono_f
    let sq := IsPullback.of_hasPullback p S.f
    let m := cokernel.map (pullback.fst p S.f) S.f (pullback.snd p S.f) p sq.w
    let := Abelian.mono_cokernel_map_of_isPullback sq
    have : Epi m := by dsimp [m]; infer_instance
    have : IsIso m := isIso_of_mono_of_epi m
    let eq : cokernel (pullback.fst p S.f) ≅ S.X₃ :=
      asIso m ≪≫ (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS'.gIsCokernel
    have hQ := P.prop_of_iso eq.symm hP
    let k := kernel.map (pullback.snd p S.f) p (pullback.fst p S.f) S.f sq.flip.w
    let := isIso_kernel_map_of_isPullback sq.flip
    have hK : inverseObjClass P h (kernel (pullback.snd p S.f)) =
        inverseObjClass P h (kernel p) := inverseObjClass_iso P h (asIso k)
    rw [inverseObjClass_mono P h (pullback.fst p S.f) hQ,
      ih (pullback.snd p S.f), hK, factorClass_iso P eq hQ hP]
    exact add_assoc _ _ _

/-- The filtration invariant is additive on every ambient short exact sequence. -/
lemma inverseObjClass_additive (h : FiltrationHypothesis P) {S : ShortComplex C}
    (hS : S.ShortExact) :
    inverseObjClass P h S.X₂ = inverseObjClass P h S.X₁ + inverseObjClass P h S.X₃ := by
  let := hS.epi_g
  let e : kernel S.g ≅ S.X₁ :=
    (kernelIsKernel S.g).conePointUniqueUpToIso hS.fIsKernel
  rw [inverseObjClass_epi_filtration P h (Classical.choice (h S.X₃)) S.g,
    inverseObjClass_iso P h e]
  rfl

/-- The inverse homomorphism to inclusion, obtained from the proved,
filtration-independent additive invariant. -/
def inverseGrothendieckMap (h : FiltrationHypothesis P) :
    (abelianExactStructure C).GrothendieckGroup →+
      (subcategoryExactStructure P).GrothendieckGroup :=
  (abelianExactStructure C).grothendieckLift (inverseObjClass P h)
    (fun _ hS => inverseObjClass_additive P h hS)

@[simp] lemma inverseGrothendieckMap_class (h : FiltrationHypothesis P) (X : C) :
    inverseGrothendieckMap P h ((abelianExactStructure C).grothendieckClass X) =
      inverseObjClass P h X :=
  (abelianExactStructure C).grothendieckLift_class _ _ X

/-- On the smaller category, the inverse sends an object's ambient class back
to its original class. -/
lemma inverseGrothendieckMap_comp (h : FiltrationHypothesis P) :
    (inverseGrothendieckMap P h).comp (grothendieckMap P) = AddMonoidHom.id _ := by
  apply (subcategoryExactStructure P).grothendieck_hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, grothendieckMap_class,
    inverseGrothendieckMap_class, AddMonoidHom.id_apply]
  exact inverseObjClass_of_mem P h X.property

lemma inverseGrothendieckMap_leftInverse (h : FiltrationHypothesis P) :
    Function.LeftInverse (inverseGrothendieckMap P h) (grothendieckMap P) := by
  intro a
  exact DFunLike.congr_fun (inverseGrothendieckMap_comp P h) a

lemma inverseGrothendieckMap_rightInverse (h : FiltrationHypothesis P) :
    Function.RightInverse (inverseGrothendieckMap P h) (grothendieckMap P) := by
  intro b
  obtain ⟨a, rfl⟩ := grothendieckMap_surjective P h b
  rw [inverseGrothendieckMap_leftInverse P h a]

/-- Algebraic dévissage injectivity. This uses genuine finite-filtration
refinement, with no extension-closure assumption on the smaller category. -/
theorem grothendieckMap_injective (h : FiltrationHypothesis P) :
    Function.Injective (grothendieckMap P) :=
  (inverseGrothendieckMap_leftInverse P h).injective

/-- Algebraic Grothendieck-group dévissage: the inclusion induces an isomorphism.
This theorem concerns the group presented by short exact sequences; it does
not identify that group with homotopical Quillen `K₀` or prove higher dévissage. -/
def grothendieckEquiv (h : FiltrationHypothesis P) :
    (subcategoryExactStructure P).GrothendieckGroup ≃+
      (abelianExactStructure C).GrothendieckGroup :=
  AddEquiv.ofBijective (grothendieckMap P)
    ⟨grothendieckMap_injective P h, grothendieckMap_surjective P h⟩

@[simp] lemma grothendieckEquiv_apply (h : FiltrationHypothesis P)
    (a : (subcategoryExactStructure P).GrothendieckGroup) :
    grothendieckEquiv P h a = grothendieckMap P a := rfl

@[simp] lemma grothendieckEquiv_symm_apply (h : FiltrationHypothesis P)
    (b : (abelianExactStructure C).GrothendieckGroup) :
    (grothendieckEquiv P h).symm b = inverseGrothendieckMap P h b := by
  apply (grothendieckEquiv P h).injective
  rw [AddEquiv.apply_symm_apply, grothendieckEquiv_apply,
    inverseGrothendieckMap_rightInverse P h b]

end Quillen.Devissage
