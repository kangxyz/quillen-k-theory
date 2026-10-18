/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Support.FiniteClosed
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Support
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Canonical finite families of singleton-supported coherent sheaves

For a locally Noetherian scheme and an injective family of closed points,
`reconstructionEquivalence` identifies the canonical
`CategoryTheory.Pi.FiniteCategoryFamily` of actual singleton-supported coherent
categories with actual coherent sheaves having finite stalk support contained
in the specified point range. Its forward functor is the coproduct in all
module sheaves of the original singleton inclusions. Finite nonzero support,
allowing arbitrary zero objects elsewhere, compares this coproduct with a
finite actual sum and proves coherence. Orthogonality gives full faithfulness;
the actual finite-stage splitting gives essential surjectivity. Both directions
are exact, and the original singleton and evaluation squares are retained.

On a Noetherian scheme, `finitePointSupport_iff_support_subset` identifies the
target predicate with ordinary support containment in the specified closed-point
range. `closedPointReconstructionEquivalence` specializes to the subtype of all
closed points, and `closedPointSupport_iff` gives the corresponding geometric
predicate. These comparisons preserve the predicates used by the coherent
second-support consumer. They introduce no alternate finite-family model.

Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Coherent.Support.FiniteClosedFamilies`.
Current consumer: Quillen's closed-point coherent support K1 assembly.
Upper-universe small-model transport, scheme K-theory and comparison with
residue-field pushforward belong to downstream adapters. Singleton-supported
coherent categories are not identified categorically with residue vector spaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

namespace AlgebraicGeometry.Scheme.Modules.Coherent.FiniteClosedFamilies
open FiniteClosedSupport

section Coproduct
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {I : Type*} (A : I → C) [HasCoproduct A] (s : Finset I)
  [HasBiproduct (fun i : s => A i.val)]

/-- The canonical finite biproduct map into the original coproduct. -/
def finiteSumToCoproduct : (⨁ fun i : s => A i.val) ⟶ ∐ A :=
  biproduct.desc (fun i : s => Sigma.ι A i.val)

/-- The canonical finite projection, zero on all coordinates outside the finite set. -/
def coproductToFiniteSum : (∐ A) ⟶ ⨁ fun i : s => A i.val :=
  Sigma.desc (fun i => if hi : i ∈ s then biproduct.ι (fun j : s => A j.val) ⟨i, hi⟩ else 0)

/-- An actual finite sum equals the original coproduct when all other objects are zero. -/
def finiteSumCoproductIso (h : ∀ i, i ∉ s → IsZero (A i)) :
    (⨁ fun i : s => A i.val) ≅ ∐ A where
  hom := finiteSumToCoproduct A s
  inv := coproductToFiniteSum A s
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro i
    simp [finiteSumToCoproduct, coproductToFiniteSum, i.property]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro i
    by_cases hi : i ∈ s
    · simp [finiteSumToCoproduct, coproductToFiniteSum, hi]
    · exact (h i hi).eq_of_src _ _

/-- The finite projection retains each original coproduct coordinate map. -/
lemma coproductToFiniteSum_π (h : ∀ i, i ∉ s → IsZero (A i)) (i : s) :
    coproductToFiniteSum A s ≫ biproduct.π (fun j : s => A j.val) i = Sigma.π A i.val := by
  apply Sigma.hom_ext
  intro j
  by_cases hji : j = i.val
  · subst j
    simp [coproductToFiniteSum, i.property]
  · by_cases hj : j ∈ s
    · have hsub : (⟨j, hj⟩ : s) ≠ i := fun h => hji (congrArg Subtype.val h)
      simp [coproductToFiniteSum, hj, hsub, Sigma.ι_π_of_ne A hji]
    · exact (h j hj).eq_of_src _ _

/-- For a finitely supported family, original coordinate projections detect morphisms. -/
lemma coproduct_hom_ext_of_finite_support (h : ∀ i, i ∉ s → IsZero (A i))
    {Z : C} (f g : Z ⟶ ∐ A) (w : ∀ i, f ≫ Sigma.π A i = g ≫ Sigma.π A i) : f = g := by
  apply (cancel_mono (finiteSumCoproductIso A s h).inv).1
  apply biproduct.hom_ext
  intro i
  simpa only [Category.assoc, finiteSumCoproductIso, coproductToFiniteSum_π A s h i] using w i.val

end Coproduct

/-- A subsheaf has support contained in the support of its target. -/
lemma support_subset_of_mono {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    support M ⊆ support N := by
  intro x hx hN
  exact hx (ObjectProperty.prop_of_mono (IsZero (C := AddCommGrpCat.{u}))
    ((stalkFunctor X x).map f) hN)

/-- A quotient sheaf has support contained in the support of its source. -/
lemma support_subset_of_epi {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    support N ⊆ support M := by
  intro x hx hM
  let : PreservesFiniteColimits (stalkFunctor X x) :=
    preservesFiniteColimits_of_natIso (moduleStalkForgetIso X x)
  exact hx (ObjectProperty.prop_of_epi (IsZero (C := AddCommGrpCat.{u}))
    ((stalkFunctor X x).map f) hM)

/-- The middle support of an actual short exact sequence lies in the union of end supports. -/
lemma support_middle_subset_union {X : Scheme.{u}} {T : ShortComplex X.Modules}
    (hT : T.ShortExact) : support T.X₂ ⊆ support T.X₁ ∪ support T.X₃ := by
  intro x hx
  let : PreservesFiniteColimits (stalkFunctor X x) :=
    preservesFiniteColimits_of_natIso (moduleStalkForgetIso X x)
  by_contra h
  have h1 : IsZero ((stalkFunctor X x).obj T.X₁) := by
    by_contra h1
    exact h (Or.inl h1)
  have h3 : IsZero ((stalkFunctor X x).obj T.X₃) := by
    by_contra h3
    exact h (Or.inr h3)
  exact hx ((hT.map_of_exact (stalkFunctor X x)).exact.isZero_of_both_isZero h1 h3)

/-- Actual finite stalk support contained in the specified geometric point range. -/
def finitePointSupport (X : Scheme.{u}) {I : Type u} (point : I → X) :
    ObjectProperty (FiniteTypeSheaves X) :=
  fun M => (support M.obj).Finite ∧ support M.obj ⊆ Set.range point

instance finitePointSupport_serre (X : Scheme.{u}) [IsLocallyNoetherian X]
    {I : Type u} (point : I → X) : (finitePointSupport X point).IsSerreClass where
  exists_zero := by
    let M : FiniteTypeSheaves X := 0
    have h0 : support M.obj = ∅ := (support_eq_empty_iff _).2
      ((finiteTypeSheavesToModules X).map_isZero (isZero_zero _))
    exact ⟨M, isZero_zero _, by simp [finitePointSupport, h0]⟩
  prop_of_mono f hf h := by
    let := hf
    have hs := support_subset_of_mono ((finiteTypeSheavesToModules X).map f)
    exact ⟨h.1.subset hs, hs.trans h.2⟩
  prop_of_epi f hf h := by
    let := hf
    have hs := support_subset_of_epi ((finiteTypeSheavesToModules X).map f)
    exact ⟨h.1.subset hs, hs.trans h.2⟩
  prop_X₂_of_shortExact h h1 h3 := by
    have hs := support_middle_subset_union (h.map_of_exact (finiteTypeSheavesToModules X))
    exact ⟨(h1.1.union h3.1).subset hs,
      hs.trans (Set.union_subset h1.2 h3.2)⟩

/-- The full category selected by the actual finite geometric support predicate. -/
abbrev FinitePointSupportCategory (X : Scheme.{u}) {I : Type u} (point : I → X) :=
  (finitePointSupport X point).FullSubcategory

section Families
variable (X : Scheme.{u}) [IsLocallyNoetherian X] {I : Type u}
  (point : I → X) (closed : ∀ i, IsClosed ({point i} : Set X))

/-- Actual coherent sheaves supported at the specified closed point. -/
abbrev PointCategory (i : I) := ClosedSupportCategory X {point i} (closed i)

/-- The original canonical category of finite-support families of singleton categories. -/
abbrev PointFamily := Pi.FiniteCategoryFamily (PointCategory X point closed)

/-- The original fully faithful singleton-support inclusion into all module sheaves. -/
abbrev pointRealization (i : I) : PointCategory X point closed i ⥤ X.Modules :=
  (closedSupportProperty X {point i} (closed i)).ι ⋙ finiteTypeSheavesToModules X

instance pointRealization_additive (i : I) : (pointRealization X point closed i).Additive where
  map_add := by intros; rfl

/-- The actual sheaves underlying a canonical finite-support family. -/
def familySheaves (A : PointFamily X point closed) : I → X.Modules :=
  fun i => (pointRealization X point closed i).obj (A.obj i)

/-- Canonical reconstruction by the coproduct of the original singleton inclusions. -/
def reconstructionModules : PointFamily X point closed ⥤ X.Modules where
  obj A := ∐ familySheaves X point closed A
  map f := Limits.Sigma.map (fun i => (pointRealization X point closed i).map (f.hom i))
  map_id A := by apply Sigma.hom_ext; intro i; simp [familySheaves, pointRealization]
  map_comp f g := by apply Sigma.hom_ext; intro i; simp [Category.assoc]

/-- The actual finite set of nonzero coordinates, without replacing other zero objects. -/
def sourceSupport (A : PointFamily X point closed) : Finset I := A.property.toFinset

omit [IsLocallyNoetherian X] in
/-- Every coordinate outside the actual support realizes as a zero sheaf. -/
lemma familySheaves_isZero_outside (A : PointFamily X point closed) (i : I)
    (hi : i ∉ sourceSupport X point closed A) : IsZero (familySheaves X point closed A i) := by
  have hz : IsZero (A.obj i) := by
    by_contra hn
    exact hi ((Set.Finite.mem_toFinset A.property).2 hn)
  exact (pointRealization X point closed i).map_isZero hz

/-- The original reconstruction coproduct is the finite sum on its actual nonzero support. -/
def reconstructionFiniteSumIso (A : PointFamily X point closed) :
    (⨁ fun i : sourceSupport X point closed A => familySheaves X point closed A i.val) ≅
      (reconstructionModules X point closed).obj A :=
  finiteSumCoproductIso (familySheaves X point closed A) (sourceSupport X point closed A)
    (familySheaves_isZero_outside X point closed A)

/-- The actual reconstruction is coherent because it is isomorphic to a finite coherent sum. -/
lemma reconstruction_coherent (A : PointFamily X point closed) :
    affineLocallyFiniteType X ((reconstructionModules X point closed).obj A) := by
  apply (affineLocallyFiniteType X).prop_of_iso (reconstructionFiniteSumIso X point closed A)
  exact (affineLocallyFiniteType X).prop_of_isColimit (biproduct.isColimit _)
    (fun i => (A.obj i.as.val).obj.property)

omit [IsLocallyNoetherian X] in
/-- Reconstruction has stalk support inside the image of its actual finite coordinate support. -/
lemma reconstruction_support_subset (A : PointFamily X point closed) :
    support ((reconstructionModules X point closed).obj A) ⊆
      point '' (sourceSupport X point closed A : Set I) := by
  rw [← support_eq_of_iso (reconstructionFiniteSumIso X point closed A)]
  intro x hx
  by_contra hn
  have hzero (i : sourceSupport X point closed A) :
      IsZero ((stalkFunctor X x).obj (familySheaves X point closed A i.val)) := by
    by_contra h
    have hp := (closedSupportProperty_iff X _ _ (A.obj i.val).obj).1 (A.obj i.val).property h
    exact hn ⟨i.val, i.property, (Set.mem_singleton_iff.mp hp).symm⟩
  have := preservesBiproduct_of_preservesProduct (stalkFunctor X x)
    (f := fun i : sourceSupport X point closed A => familySheaves X point closed A i.val)
  have hz : IsZero ((stalkFunctor X x).obj
      (⨁ fun i : sourceSupport X point closed A => familySheaves X point closed A i.val)) :=
    ObjectProperty.prop_of_isLimit (IsZero (C := AddCommGrpCat.{u}))
      (isLimitOfPreserves (stalkFunctor X x) (biproduct.isLimit _)) (fun i => hzero i.as)
  exact hx hz

/-- Original singleton summation, with its actual coherent finite-support codomain. -/
def reconstruction : PointFamily X point closed ⥤ FinitePointSupportCategory X point :=
  (finitePointSupport X point).lift
    ((affineLocallyFiniteType X).lift (reconstructionModules X point closed)
      (reconstruction_coherent X point closed)) (fun A =>
    ⟨((sourceSupport X point closed A).finite_toSet.image point).subset
        (reconstruction_support_subset X point closed A),
      (reconstruction_support_subset X point closed A).trans (Set.image_subset_range _ _)⟩)

instance pointRealization_full (i : I) : (pointRealization X point closed i).Full := by
  dsimp [pointRealization]
  infer_instance

instance pointRealization_faithful (i : I) : (pointRealization X point closed i).Faithful := by
  dsimp [pointRealization]
  infer_instance

/-- Singleton-support orthogonality lifts every actual reconstruction morphism coordinatewise. -/
theorem reconstructionFull (injective : Function.Injective point) :
    (reconstruction X point closed).Full where
  map_surjective {A B} f := by
    let g : A ⟶ B := (Pi.finiteObjectSupport (PointCategory X point closed)).homMk
      (fun i => (pointRealization X point closed i).preimage
        (Sigma.ι (familySheaves X point closed A) i ≫ f.hom.hom ≫
          Sigma.π (familySheaves X point closed B) i))
    refine ⟨g, ?_⟩
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Sigma.hom_ext
    intro i
    apply coproduct_hom_ext_of_finite_support (familySheaves X point closed B)
      (sourceSupport X point closed B) (familySheaves_isZero_outside X point closed B)
    intro j
    by_cases hij : i = j
    · subst j
      suffices hdiag : ((pointRealization X point closed i).preimage
          (Sigma.ι (familySheaves X point closed A) i ≫ f.hom.hom ≫
            Sigma.π (familySheaves X point closed B) i)).hom.hom =
          Sigma.ι (familySheaves X point closed A) i ≫ f.hom.hom ≫
            Sigma.π (familySheaves X point closed B) i by
        simpa [reconstruction, reconstructionModules, g] using hdiag
      exact (pointRealization X point closed i).map_preimage _
    · have hzero := hom_eq_zero_of_singleton_support (point i) (point j) (closed j)
        (fun h => hij (injective h))
        ((closedSupportProperty_iff X _ _ (A.obj i).obj).1 (A.obj i).property)
        ((closedSupportProperty_iff X _ _ (B.obj j).obj).1 (B.obj j).property)
        (Sigma.ι (familySheaves X point closed A) i ≫ f.hom.hom ≫
          Sigma.π (familySheaves X point closed B) j)
      simpa [reconstruction, reconstructionModules, Sigma.ι_π_of_ne _ hij] using hzero.symm

instance reconstruction_faithful : (reconstruction X point closed).Faithful where
  map_injective {A B} f g h := by
    apply ObjectProperty.hom_ext
    funext i
    apply (pointRealization X point closed i).map_injective
    have hi := congrArg (fun k => Sigma.ι (familySheaves X point closed A) i ≫
      k.hom.hom ≫ Sigma.π (familySheaves X point closed B) i) h
    simpa [reconstruction, reconstructionModules] using hi

/-- The finite-stage splitting supplies an actual family for every supported coherent sheaf. -/
theorem reconstructionEssSurj (injective : Function.Injective point) :
    (reconstruction X point closed).EssSurj where
  mem_essImage M := by
    let S := M.property.1.toFinset
    have hMS : support M.obj.obj ⊆ (S : Set X) := by
      intro x hx
      exact (Set.Finite.mem_toFinset M.property.1).2 hx
    have hS (x : X) (hx : x ∈ S) : IsClosed ({x} : Set X) := by
      obtain ⟨i, hi⟩ := M.property.2 ((Set.Finite.mem_toFinset M.property.1).1 hx)
      exact hi ▸ closed i
    let Bpos (i : I) (hi : point i ∈ S) : Σ N : PointCategory X point closed i,
        (pointRealization X point closed i).obj N ⟶ M.obj.obj :=
      ⟨⟨⟨(componentFunctor X S hS ⟨point i, hi⟩).obj M.obj.obj,
            component_coherent X S hS ⟨point i, hi⟩ M.obj hMS⟩,
          (closedSupportProperty_iff X _ _ _).2
            (component_support_subset X S hS ⟨point i, hi⟩ M.obj.obj hMS)⟩,
          (componentCounit X S hS ⟨point i, hi⟩).app M.obj.obj⟩
    let B : ∀ i : I, Σ N : PointCategory X point closed i,
        (pointRealization X point closed i).obj N ⟶ M.obj.obj := fun i =>
      if hi : point i ∈ S then Bpos i hi else ⟨0, 0⟩
    have hpre : (point ⁻¹' (S : Set X)).Finite := S.finite_toSet.preimage injective.injOn
    let A : PointFamily X point closed := ⟨fun i => (B i).1, hpre.subset (by
      intro i hi
      by_contra hn
      change point i ∉ S at hn
      exact hi (by simp only [B, dite_eq_right hn]; exact isZero_zero _))⟩
    let f : (reconstructionModules X point closed).obj A ⟶ M.obj.obj :=
      Sigma.desc (fun i => (B i).2)
    have hf : IsIso f := by
      apply isIso_of_moduleStalk
      intro x
      let T := moduleStalk X x
      let : T.IsLeftAdjoint := (moduleStalkSkyscraperAdjunction X x).isLeftAdjoint
      apply (isIso_comp_left_iff (sigmaComparison T (familySheaves X point closed A)) _).1
      change IsIso (sigmaComparison T (familySheaves X point closed A) ≫
        T.map (Sigma.desc (fun i => (B i).2)))
      rw [sigmaComparison_map_desc]
      by_cases hx : x ∈ S
      · obtain ⟨i, hi⟩ := M.property.2 ((Set.Finite.mem_toFinset M.property.1).1 hx)
        have hiS : point i ∈ S := hi ▸ hx
        have hfi : IsIso (T.map ((B i).2)) := by
          have hBi : B i = Bpos i hiS := dite_eq_left hiS
          rw [hBi]
          exact componentCounit_stalk_isIso X S hS ⟨point i, hiS⟩ M.obj.obj x
            ((mem_isolatingOpen X S hS _ x).2 (Or.inr hi.symm))
        have hz (j : I) (hji : j ≠ i) :
            IsZero (T.obj (familySheaves X point closed A j)) := by
          apply moduleStalk_isZero_of_not_mem_support
          intro hj
          have hj' := Set.mem_singleton_iff.mp
            ((closedSupportProperty_iff X _ _ (A.obj j).obj).1 (A.obj j).property hj)
          exact hji (injective (hj'.symm.trans hi.symm))
        let : IsIso (T.map ((B i).2)) := hfi
        refine ⟨⟨inv (T.map ((B i).2)) ≫
          Sigma.ι (fun j => T.obj (familySheaves X point closed A j)) i, ?_, ?_⟩⟩
        · apply Sigma.hom_ext
          intro j
          by_cases hji : j = i
          · subst j; simp
          · exact (hz j hji).eq_of_src _ _
        · simp
      · have hzero : IsZero (T.obj M.obj.obj) :=
          moduleStalk_isZero_of_not_mem_support _ x (fun h => hx (hMS h))
        have hz (j : I) : IsZero (T.obj (familySheaves X point closed A j)) := by
          by_cases hjS : point j ∈ S
          · apply moduleStalk_isZero_of_not_mem_support
            intro hj
            have hj' := Set.mem_singleton_iff.mp
              ((closedSupportProperty_iff X _ _ (A.obj j).obj).1 (A.obj j).property hj)
            exact hx (hj' ▸ hjS)
          · have hjzero : IsZero (A.obj j) := by
              change IsZero (B j).1
              simp only [B, dite_eq_right hjS]
              exact isZero_zero _
            exact T.map_isZero ((pointRealization X point closed j).map_isZero hjzero)
        have hsum : IsZero (∐ fun j => T.obj (familySheaves X point closed A j)) := by
          apply (IsZero.iff_id_eq_zero _).2
          apply Sigma.hom_ext
          intro j
          exact (hz j).eq_of_src _ _
        exact hsum.isIso hzero _
    let H := (finitePointSupport X point).ι ⋙ finiteTypeSheavesToModules X
    exact ⟨A, ⟨H.preimageIso (asIso f)⟩⟩

/-- Canonical singleton summation gives the genuine finite closed-support equivalence. -/
def reconstructionEquivalence (injective : Function.Injective point) :
    PointFamily X point closed ≌ FinitePointSupportCategory X point := by
  let := reconstructionFull X point closed injective
  let := reconstructionEssSurj X point closed injective
  let : (reconstruction X point closed).IsEquivalence := {}
  exact (reconstruction X point closed).asEquivalence

/-- The proved original reconstruction equivalence preserves the additive structure. -/
theorem reconstruction_additive (injective : Function.Injective point) :
    (reconstruction X point closed).Additive := by
  let : (reconstruction X point closed).IsEquivalence :=
    (reconstructionEquivalence X point closed injective).isEquivalence_functor
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (reconstruction X point closed)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Original reconstruction is exact for the standard abelian exact structures. -/
def reconstructionExactFunctor (injective : Function.Injective point) :
    CategoryTheory.ExactCategory.ExactFunctor
      (Pi.finiteCategoryExactStructure (PointCategory X point closed))
      (ObjectProperty.subcategoryExactStructure (finitePointSupport X point)) where
  toFunctor := reconstruction X point closed
  additive := reconstruction_additive X point closed injective
  map_conflation _ h := by
    let : (reconstruction X point closed).IsEquivalence :=
      (reconstructionEquivalence X point closed injective).isEquivalence_functor
    exact h.map_of_exact _

instance reconstructionExactFunctor_isEquivalence (injective : Function.Injective point) :
    (reconstructionExactFunctor X point closed injective).toFunctor.IsEquivalence :=
  (reconstructionEquivalence X point closed injective).isEquivalence_functor

/-- The inverse of actual reconstruction is exact. -/
def decompositionExactFunctor (injective : Function.Injective point) :
    CategoryTheory.ExactCategory.ExactFunctor
      (ObjectProperty.subcategoryExactStructure (finitePointSupport X point))
      (Pi.finiteCategoryExactStructure (PointCategory X point closed)) where
  toFunctor := (reconstructionEquivalence X point closed injective).inverse
  additive := by
    let : (reconstructionEquivalence X point closed injective).functor.Additive :=
      reconstruction_additive X point closed injective
    exact (reconstructionEquivalence X point closed injective).inverse_additive
  map_conflation _ h := h.map_of_exact _

instance decompositionExactFunctor_isEquivalence (injective : Function.Injective point) :
    (decompositionExactFunctor X point closed injective).toFunctor.IsEquivalence :=
  (reconstructionEquivalence X point closed injective).isEquivalence_inverse

/-- The original singleton inclusion into the actual finite-support coherent category. -/
def pointInclusion (i : I) : PointCategory X point closed i ⥤ FinitePointSupportCategory X point :=
  ObjectProperty.ιOfLE (fun N hN => by
    have hs := (closedSupportProperty_iff X _ _ N).1 hN
    exact ⟨(Set.finite_singleton (point i)).subset hs,
      fun x hx => ⟨i, (Set.mem_singleton_iff.mp (hs hx)).symm⟩⟩)

instance pointInclusion_additive (i : I) : (pointInclusion X point closed i).Additive where
  map_add := by intros; rfl

/-- The original singleton inclusion is exact. -/
def pointInclusionExactFunctor (i : I) : CategoryTheory.ExactCategory.ExactFunctor
    (ObjectProperty.subcategoryExactStructure (closedSupportProperty X {point i} (closed i)))
    (ObjectProperty.subcategoryExactStructure (finitePointSupport X point)) where
  toFunctor := pointInclusion X point closed i
  map_conflation _ h := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (finitePointSupport X point).ι
    let := ObjectProperty.inclusion_preservesFiniteLimits
      (closedSupportProperty X {point i} (closed i))
    let := ObjectProperty.inclusion_preservesFiniteColimits
      (closedSupportProperty X {point i} (closed i))
    exact h.map_of_exact (closedSupportProperty X {point i} (closed i)).ι

/-- A coproduct inclusion is invertible with arbitrary zero objects on all other coordinates. -/
lemma isIso_coproduct_ι_of_single {C : Type*} [Category* C] [HasZeroMorphisms C]
    {J : Type*} (A : J → C) [HasCoproduct A] (i : J)
    (h : ∀ j, j ≠ i → IsZero (A j)) : IsIso (Sigma.ι A i) := by
  refine ⟨⟨Sigma.π A i, by simp, ?_⟩⟩
  apply Sigma.hom_ext
  intro j
  by_cases hji : j = i
  · subst j; simp
  · exact (h j hji).eq_of_src _ _

omit [IsLocallyNoetherian X] in
/-- The original singleton reconstruction retains arbitrary zero objects off-coordinate. -/
lemma reconstruction_singleton_ι_isIso (A : PointFamily X point closed) (i : I)
    (hA : ∀ j, j ≠ i → IsZero (A.obj j)) :
    IsIso (Sigma.ι (familySheaves X point closed A) i) :=
  isIso_coproduct_ι_of_single _ i
    (fun j hj => (pointRealization X point closed j).map_isZero (hA j hj))

/-- Original singleton realization agrees with its canonical reconstruction in all sheaves. -/
def singletonReconstructionModulesIso (i : I) :
    pointRealization X point closed i ≅
      Pi.singletonInclusion (PointCategory X point closed) i ⋙
        reconstructionModules X point closed := by
  let e := eqToIso (Pi.singletonInclusion_comp_evaluation (PointCategory X point closed) i)
  refine NatIso.ofComponents (fun M => ?_) ?_
  · let A := (Pi.singletonInclusion (PointCategory X point closed) i).obj M
    let := reconstruction_singleton_ι_isIso X point closed A i
      (fun j hj => Pi.singletonInclusion_obj_isZero (PointCategory X point closed) i j hj M)
    exact (pointRealization X point closed i).mapIso (e.app M).symm ≪≫
      asIso (Sigma.ι (familySheaves X point closed A) i)
  · intro M N f
    dsimp
    simpa [reconstructionModules, Category.assoc] using
      congrArg (fun g => (pointRealization X point closed i).map g ≫
        Sigma.ι (familySheaves X point closed
          ((Pi.singletonInclusion (PointCategory X point closed) i).obj N)) i)
          (e.inv.naturality f)

/-- Original singleton inclusion agrees naturally with the canonical reconstruction functor. -/
def singletonReconstructionIso (i : I) :
    pointInclusion X point closed i ≅
      Pi.singletonInclusion (PointCategory X point closed) i ⋙ reconstruction X point closed :=
  Functor.fullyFaithfulCancelRight
    ((finitePointSupport X point).ι ⋙ finiteTypeSheavesToModules X)
    (singletonReconstructionModulesIso X point closed i)

/-- The chosen inverse reconstruction retains the original canonical singleton family. -/
def pointInclusionDecompositionIso (injective : Function.Injective point) (i : I) :
    pointInclusion X point closed i ⋙ (reconstructionEquivalence X point closed injective).inverse ≅
      Pi.singletonInclusion (PointCategory X point closed) i :=
  Functor.isoWhiskerRight (singletonReconstructionIso X point closed i)
      (reconstructionEquivalence X point closed injective).inverse ≪≫
    Functor.isoWhiskerLeft (Pi.singletonInclusion (PointCategory X point closed) i)
      (reconstructionEquivalence X point closed injective).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- An exact coordinate of the chosen inverse of original reconstruction. -/
def evaluationExactFunctor (injective : Function.Injective point) (i : I) :
    CategoryTheory.ExactCategory.ExactFunctor
      (ObjectProperty.subcategoryExactStructure (finitePointSupport X point))
      (ObjectProperty.subcategoryExactStructure (closedSupportProperty X {point i} (closed i))) :=
  (decompositionExactFunctor X point closed injective).comp
    (Pi.finiteCategoryEvaluation (PointCategory X point closed) i)

/-- An original singleton inclusion followed by its own exact evaluation is the identity. -/
def pointInclusionEvaluationSelfIso (injective : Function.Injective point) (i : I) :
    pointInclusion X point closed i ⋙
      (evaluationExactFunctor X point closed injective i).toFunctor ≅
      𝟭 (PointCategory X point closed i) :=
  Functor.isoWhiskerRight (pointInclusionDecompositionIso X point closed injective i)
      (Pi.finiteCategoryEvaluation (PointCategory X point closed) i).toFunctor ≪≫
    eqToIso (Pi.singletonInclusion_comp_evaluation (PointCategory X point closed) i)

/-- An original singleton inclusion has a zero object at every other exact evaluation. -/
def pointInclusionEvaluationOtherIso (injective : Function.Injective point)
    (i j : I) (hji : j ≠ i) :
    pointInclusion X point closed i ⋙
      (evaluationExactFunctor X point closed injective j).toFunctor ≅
      (Functor.const (PointCategory X point closed i)).obj (0 : PointCategory X point closed j) :=
  Functor.isoWhiskerRight (pointInclusionDecompositionIso X point closed injective i)
      (Pi.finiteCategoryEvaluation (PointCategory X point closed) j).toFunctor ≪≫
    eqToIso (Pi.singletonInclusion_comp_evaluation_zero (PointCategory X point closed) i j hji)

omit [IsLocallyNoetherian X] in
/-- On a Noetherian scheme, coherent support in a range of closed points is finite. -/
theorem support_finite_of_closed_range [IsNoetherian X]
    (closed : ∀ i, IsClosed ({point i} : Set X)) (M : FiniteTypeSheaves X)
    (hs : support M.obj ⊆ Set.range point) : (support M.obj).Finite := by
  let Z := support M.obj
  have hZ : IsClosed Z := finiteType_support_isClosed M
  obtain ⟨S, hS, hSc, hSi, hSZ⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  let g : S → X := fun s => (hSi s.val s.property).genericPoint
  let : Finite S := hS.to_subtype
  apply (Set.finite_range g).subset
  intro x hx
  change x ∈ Z at hx
  obtain ⟨s, hsS, hxs⟩ := Set.mem_sUnion.mp (hSZ ▸ hx)
  let t : S := ⟨s, hsS⟩
  have hg : IsGenericPoint (g t) s := (hSi s hsS).isGenericPoint_genericPoint (hSc s hsS)
  have hgZ : g t ∈ Z := by
    rw [hSZ]
    exact Set.mem_sUnion.mpr ⟨s, hsS, hg.mem⟩
  obtain ⟨i, hi⟩ := hs hgZ
  have hc : IsClosed ({g t} : Set X) := hi ▸ closed i
  have heq : x = g t := (hg.specializes hxs).mem_closed hc (Set.mem_singleton _)
  exact ⟨t, heq.symm⟩

omit [IsLocallyNoetherian X] in
/-- The finite support predicate agrees with ordinary range support on a Noetherian scheme. -/
theorem finitePointSupport_iff_support_subset [IsNoetherian X]
    (closed : ∀ i, IsClosed ({point i} : Set X)) (M : FiniteTypeSheaves X) :
    finitePointSupport X point M ↔ support M.obj ⊆ Set.range point :=
  ⟨fun h => h.2, fun h => ⟨support_finite_of_closed_range X point closed M h, h⟩⟩

end Families

/-- The canonical subtype of geometric closed points. -/
abbrev ClosedPoint (X : Scheme.{u}) := {x : X // IsClosed ({x} : Set X)}

/-- Original finite-family reconstruction for the canonical index of all closed points. -/
def closedPointReconstructionEquivalence (X : Scheme.{u}) [IsLocallyNoetherian X] :
    PointFamily X (fun x : ClosedPoint X => x.val) (fun x => x.property) ≌
      FinitePointSupportCategory X (fun x : ClosedPoint X => x.val) :=
  reconstructionEquivalence X (fun x : ClosedPoint X => x.val) (fun x => x.property)
    Subtype.val_injective

/-- On a Noetherian scheme, the canonical target is exactly coherent closed-point support. -/
theorem closedPointSupport_iff (X : Scheme.{u}) [IsNoetherian X] (M : FiniteTypeSheaves X) :
    finitePointSupport X (fun x : ClosedPoint X => x.val) M ↔
      ∀ x ∈ support M.obj, IsClosed ({x} : Set X) := by
  rw [finitePointSupport_iff_support_subset X _ (fun x => x.property)]
  constructor
  · intro h x hx
    obtain ⟨i, hi⟩ := h hx
    exact hi ▸ i.property
  · intro h x hx
    exact ⟨⟨x, h x hx⟩, rfl⟩

end AlgebraicGeometry.Scheme.Modules.Coherent.FiniteClosedFamilies
