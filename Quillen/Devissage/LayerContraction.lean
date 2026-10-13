/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Devissage.Layers
public import Quillen.Topology.ClassifyingSpace.Equivalence

/-!
# Contraction of the dévissage layer category

Intersection gives the one-step homotopy equivalence in Quillen's proof.
Induction over an actual finite filtration then contracts the layer category.
-/
@[expose] public section


noncomputable section
universe v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace Quillen.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]
  (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts]

namespace Layer
variable {P} {M : C}

/-- Inclusion of layers supported in a smaller subobject. -/
def supportedInclusion {A N : Subobject M} (hAN : A ≤ N) :
    Supported (P := P) A ⥤ Supported (P := P) N :=
  (show Monotone (fun L : Supported (P := P) A =>
    (⟨L.val, L.property.trans hAN⟩ : Supported (P := P) N)) from
    fun _ _ h => h).functor

/-- Intersect a supported layer with the smaller ambient subobject. -/
def supportedRestriction (A N : Subobject M) :
    Supported (P := P) N ⥤ Supported (P := P) A :=
  (show Monotone (fun L : Supported (P := P) N =>
    (⟨restrict A L.val, inf_le_right⟩ : Supported (P := P) A)) from
    fun _ _ h => restrict_mono A h).functor

/-- The intermediate enlargement functor appearing in the contraction zigzag. -/
def supportedEnlargement {A N : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    Supported (P := P) N ⥤ Supported (P := P) N :=
  (enlarge_mono hAN hA).functor

/-- Restricting a layer already supported in `A` does nothing. -/
def supportedRestrictionUnit {A N : Subobject M} (hAN : A ≤ N) :
    supportedInclusion (P := P) hAN ⋙ supportedRestriction A N ≅
      𝟭 (Supported (P := P) A) :=
  NatIso.ofComponents (fun L => eqToIso (by
    apply Subtype.ext
    apply Layer.ext
    · exact inf_eq_left.mpr (L.val.le.trans L.property)
    · exact inf_eq_left.mpr L.property)) (by intros; apply Subsingleton.elim)

/-- The restricted layer maps into the intermediate enlargement. -/
def supportedRestrictionToEnlargement {A N : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    supportedRestriction (P := P) A N ⋙ supportedInclusion hAN ⟶
      supportedEnlargement hAN hA where
  app L := homOfLE ⟨le_rfl, inf_le_left⟩

/-- The original layer maps into the same intermediate enlargement. -/
def supportedIdToEnlargement {A N : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    𝟭 (Supported (P := P) N) ⟶ supportedEnlargement hAN hA where
  app L := homOfLE ⟨inf_le_left, le_rfl⟩

/-- Quillen's one-filtration-step equivalence, with actual continuous homotopies
and the inclusion as its forward map. -/
def supportedStepHomotopyEquiv {A N : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (Supported (P := P) A))
      (ClassifyingSpace (Supported (P := P) N)) where
  toFun := (classifyingSpaceMap (supportedInclusion (P := P) hAN)).hom
  invFun := (classifyingSpaceMap (supportedRestriction (P := P) A N)).hom
  left_inv := by
    simpa only [classifyingSpaceMap_comp, classifyingSpaceMap_id, TopCat.hom_comp,
      TopCat.hom_id] using
      (show (classifyingSpaceMap (supportedInclusion (P := P) hAN ⋙
        supportedRestriction A N)).hom.Homotopic
          (classifyingSpaceMap (𝟭 (Supported (P := P) A))).hom from
        ⟨classifyingSpaceNaturalTransformationHomotopy
          (supportedRestrictionUnit (P := P) hAN).hom⟩)
  right_inv := by
    have h₁ := classifyingSpaceNaturalTransformationHomotopy
      (supportedRestrictionToEnlargement (P := P) hAN hA)
    have h₂ := classifyingSpaceNaturalTransformationHomotopy
      (supportedIdToEnlargement (P := P) hAN hA)
    simpa only [classifyingSpaceMap_comp, classifyingSpaceMap_id, TopCat.hom_comp,
      TopCat.hom_id] using (ContinuousMap.Homotopic.trans ⟨h₁⟩ ⟨h₂.symm⟩)

/-- The degenerate layer with both endpoints equal. -/
def diagonal (N : Subobject M) : Layer P M where
  lower := N
  upper := N
  le := le_rfl
  property := by
    have h : Subobject.ofLE N N le_rfl = 𝟙 (N : C) := by simp
    rw [h]
    exact P.prop_of_isZero (isZero_cokernel_of_epi (𝟙 (N : C)))

/-- The zero-supported layer category has a terminal object. -/
def supportedBottomIsTerminal :
    IsTerminal (⟨diagonal (P := P) (⊥ : Subobject M), le_rfl⟩ : Supported (P := P) ⊥) :=
  IsTerminal.ofUniqueHom (fun L => homOfLE ⟨bot_le, L.property⟩)
    (by intros; apply Subsingleton.elim)

omit [P.IsClosedUnderSubobjects] [P.IsClosedUnderFiniteProducts] in
/-- The base of finite-filtration induction is genuinely contractible. -/
theorem supportedBottom_contractible :
    ContractibleSpace (ClassifyingSpace (Supported (P := P) (⊥ : Subobject M))) :=
  classifyingSpace_contractible_of_isTerminal (supportedBottomIsTerminal (P := P))


/-- Any finite admissible filtration contracts the layer category supported
on its image under any ambient monomorphism. -/
theorem supported_contractible_of_filtration {X M : C}
    (F : (abelianExactStructure C).Filtration P X) (j : X ⟶ M) [Mono j] :
    ContractibleSpace (ClassifyingSpace (Supported (P := P) (Subobject.mk j))) := by
  induction F generalizing M with
  | zero hX =>
    have h : Subobject.mk j = ⊥ := Subobject.mk_eq_bot_iff_zero.mpr (hX.eq_of_src _ _)
    rw [h]
    exact supportedBottom_contractible
  | step S hS F hP ih =>
    have hS' : S.ShortExact := hS
    let := hS'.mono_f
    let A := Subobject.mk (S.f ≫ j)
    let N := Subobject.mk j
    have hAN : A ≤ N := Subobject.mk_le_mk_of_comm S.f rfl
    let e : cokernel (Subobject.ofLE A N hAN) ≅ cokernel S.f :=
      cokernel.mapIso _ _ (Subobject.underlyingIso (S.f ≫ j))
        (Subobject.underlyingIso j) (by
          apply (cancel_mono j).1
          simp [A, N, assoc])
    let e' : cokernel S.f ≅ S.X₃ :=
      (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS'.gIsCokernel
    have hA : P (cokernel (Subobject.ofLE A N hAN)) :=
      P.prop_of_iso (e.trans e').symm hP
    let : ContractibleSpace (ClassifyingSpace (Supported (P := P) A)) := ih (S.f ≫ j)
    exact (supportedStepHomotopyEquiv hAN hA).symm.contractibleSpace

/-- Supporting layers in the maximal subobject imposes no restriction. -/
def supportedTopEquivalence : Supported (P := P) (⊤ : Subobject M) ≌ Layer P M where
  functor :=
    { obj := fun L => L.val
      map := fun f => homOfLE (leOfHom f) }
  inverse :=
    { obj := fun L => ⟨L, le_top⟩
      map := fun f => homOfLE (leOfHom f) }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; apply Subsingleton.elim)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; apply Subsingleton.elim)

/-- The layer category in Quillen's dévissage proof is contractible whenever
the ambient object has a finite filtration with factors in `P`. -/
theorem contractible_of_filtration {M : C}
    (F : (abelianExactStructure C).Filtration P M) :
    ContractibleSpace (ClassifyingSpace (Layer P M)) := by
  have h := supported_contractible_of_filtration F (𝟙 M)
  rw [Subobject.mk_eq_top_of_isIso] at h
  let := h
  exact (equivalenceClassifyingHomotopyEquiv
    (supportedTopEquivalence (P := P) (M := M))).symm.contractibleSpace

end Layer
end Quillen.Devissage
