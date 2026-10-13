/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.InjectivePushforwardAdjunction
public import Quillen.Algebra.Homology.KInjectiveMap

/-! # Original injective-target direct-image model changes

The genuine target-sensitive Hom adjunction and the original restriction/direct-
image counit give an additive Hom equivalence. Its inverse is the actual action
on K-injective-target homotopy classes. The source is unrestricted, while the
target is genuinely lower-bounded and termwise injective.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes
/-- The standard derived model used for the original injective model comparison. -/
local instance modelChangeStandardDerived (Y : Scheme.{u}) : HasDerivedCategory.{u+1} Y.Modules :=
  HasDerivedCategory.standard _
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Original direct-image Hom equivalence with an unrestricted local source and actual injective
  target. -/
def injectivePushforwardHomEquiv (I J : Complex U) (b : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n)) :
    ((toDerived X).obj ((pushforwardComplex j).obj I) ⟶
      (toDerived X).obj ((pushforwardComplex j).obj J)) ≃+
      ((toDerived U).obj I ⟶ (toDerived U).obj J) :=
  { toFun α := (toDerived U).map ((pushforwardComplexRestrictIso j).inv.app I) ≫
      pushforwardDerivedHomEquiv j ((pushforwardComplex j).obj I) J b hJ iJ α
    invFun β := (pushforwardDerivedHomEquiv j ((pushforwardComplex j).obj I) J b hJ iJ).symm
      ((toDerived U).map ((pushforwardComplexRestrictIso j).hom.app I) ≫ β)
    left_inv α := by
      apply (pushforwardDerivedHomEquiv j ((pushforwardComplex j).obj I) J b hJ iJ).injective
      simp only [AddEquiv.apply_symm_apply, ← Category.assoc,
        ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
      erw [(toDerived U).map_id]
      exact Category.id_comp _
    right_inv β := by
      simp only [AddEquiv.apply_symm_apply, ← Category.assoc,
        ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
      erw [(toDerived U).map_id]
      exact Category.id_comp _
    map_add' α β := by simp [Preadditive.comp_add] }

/-- The equivalence is actual derived restriction conjugated by the original counits. -/
lemma injectivePushforwardHomEquiv_eq (I J : Complex U) (b : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (α : (toDerived X).obj ((pushforwardComplex j).obj I) ⟶
      (toDerived X).obj ((pushforwardComplex j).obj J)) :
    injectivePushforwardHomEquiv j I J b hJ iJ α =
      (toDerived U).map ((pushforwardComplexRestrictIso j).inv.app I) ≫
        restrictDerivedHom j α ≫
          (toDerived U).map ((pushforwardComplexRestrictIso j).hom.app J) := by
  exact congrArg (fun t => (toDerived U).map ((pushforwardComplexRestrictIso j).inv.app I) ≫ t)
    (pushforwardDerivedHomEquiv_eq_original_counit j ((pushforwardComplex j).obj I) J b hJ iJ α)

/-- An actual pushed-forward chain map is sent to the original local derived map. -/
@[simp]
lemma injectivePushforwardHomEquiv_map (I J : Complex U) (b : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n)) (f : I ⟶ J) :
    injectivePushforwardHomEquiv j I J b hJ iJ
      ((toDerived X).map ((pushforwardComplex j).map f)) = (toDerived U).map f := by
  rw [injectivePushforwardHomEquiv_eq, restrictDerivedHom_map,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  have h := (pushforwardComplexRestrictIso j).hom.naturality f
  change (restrict j).map ((pushforwardComplex j).map f) ≫
    (pushforwardComplexRestrictIso j).hom.app J =
      (pushforwardComplexRestrictIso j).hom.app I ≫ f at h
  rw [h, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- The inverse equivalence agrees with the genuine homotopy-class action of ordinary direct image.
-/
lemma injectivePushforwardHomEquiv_symm_eq (I J : Complex U) (b : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (α : (toDerived U).obj I ⟶ (toDerived U).obj J) :
    (injectivePushforwardHomEquiv j I J b hJ iJ).symm α =
      letI := isKInjective_of_lowerBounded_injective J b hJ iJ
      Quillen.CochainComplex.mapDerivedHomOfKInjective (Scheme.Modules.pushforward j) I J α := by
  let := isKInjective_of_lowerBounded_injective J b hJ iJ
  obtain ⟨f, hf⟩ := Quillen.CochainComplex.exists_chain_representative_of_isKInjective α
  change (toDerived U).map f = α at hf
  rw [← hf]
  have hm := Quillen.CochainComplex.mapDerivedHomOfKInjective_map (Scheme.Modules.pushforward j) I J
    f
  change Quillen.CochainComplex.mapDerivedHomOfKInjective (Scheme.Modules.pushforward j) I J
    ((toDerived U).map f) = (toDerived X).map ((pushforwardComplex j).map f) at hm
  rw [hm]
  apply (injectivePushforwardHomEquiv j I J b hJ iJ).injective
  rw [AddEquiv.apply_symm_apply, injectivePushforwardHomEquiv_map]

/-- The inverse comparison preserves the original direct image of every chain map. -/
@[simp]
lemma injectivePushforwardHomEquiv_symm_map (I J : Complex U) (b : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n)) (f : I ⟶ J) :
    (injectivePushforwardHomEquiv j I J b hJ iJ).symm ((toDerived U).map f) =
      (toDerived X).map ((pushforwardComplex j).map f) := by
  apply (injectivePushforwardHomEquiv j I J b hJ iJ).injective
  rw [AddEquiv.apply_symm_apply, injectivePushforwardHomEquiv_map]

/-- Original Hom transposition is natural under every genuine derived target-model map. -/
lemma pushforwardDerivedHomEquiv_postcomp_derived (K : Complex X) (I J : Complex U) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj ((pushforwardComplex j).obj I))
    (β : (toDerived U).obj I ⟶ (toDerived U).obj J) :
    pushforwardDerivedHomEquiv j K J b hJ iJ
        (φ ≫ (injectivePushforwardHomEquiv j I J b hJ iJ).symm β) =
      pushforwardDerivedHomEquiv j K I a hI iI φ ≫ β := by
  let := isKInjective_of_lowerBounded_injective J b hJ iJ
  obtain ⟨f, hf⟩ := Quillen.CochainComplex.exists_chain_representative_of_isKInjective β
  change (toDerived U).map f = β at hf
  rw [← hf, injectivePushforwardHomEquiv_symm_map]
  exact pushforwardDerivedHomEquiv_postcomp j K I J a b hI iI hJ iJ φ f

/-- Direct-image model change retains actual original derived composition. -/
lemma injectivePushforwardHomEquiv_symm_comp (I J L : Complex U) (b c : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (hL : ∀ n, n < c → IsZero (L.X n)) (iL : ∀ n, Injective (L.X n))
    (α : (toDerived U).obj I ⟶ (toDerived U).obj J)
    (β : (toDerived U).obj J ⟶ (toDerived U).obj L) :
    (injectivePushforwardHomEquiv j I L c hL iL).symm (α ≫ β) =
      (injectivePushforwardHomEquiv j I J b hJ iJ).symm α ≫
        (injectivePushforwardHomEquiv j J L c hL iL).symm β := by
  let := isKInjective_of_lowerBounded_injective J b hJ iJ
  let := isKInjective_of_lowerBounded_injective L c hL iL
  obtain ⟨f, hf⟩ := Quillen.CochainComplex.exists_chain_representative_of_isKInjective α
  obtain ⟨g, hg⟩ := Quillen.CochainComplex.exists_chain_representative_of_isKInjective β
  change (toDerived U).map f = α at hf
  change (toDerived U).map g = β at hg
  rw [← hf, ← hg, ← CategoryTheory.Functor.map_comp,
    injectivePushforwardHomEquiv_symm_map, injectivePushforwardHomEquiv_symm_map,
    injectivePushforwardHomEquiv_symm_map, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]

/-- The actual original identity is unchanged by injective-model direct image. -/
@[simp]
lemma injectivePushforwardHomEquiv_symm_id (I : Complex U) (a : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n)) :
    (injectivePushforwardHomEquiv j I I a hI iI).symm (𝟙 _) = 𝟙 _ := by
  simpa using injectivePushforwardHomEquiv_symm_map j I I a hI iI (𝟙 I)

/-- Genuine derived isomorphisms of injective models induce genuine original direct-image
  isomorphisms. -/
lemma isIso_injectivePushforwardHomEquiv_symm (I J : Complex U) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (α : (toDerived U).obj I ⟶ (toDerived U).obj J) [IsIso α] :
    IsIso ((injectivePushforwardHomEquiv j I J b hJ iJ).symm α) := by
  refine ⟨⟨(injectivePushforwardHomEquiv j J I a hI iI).symm (inv α), ?_, ?_⟩⟩
  · rw [← injectivePushforwardHomEquiv_symm_comp, IsIso.hom_inv_id,
      injectivePushforwardHomEquiv_symm_id]
  · rw [← injectivePushforwardHomEquiv_symm_comp, IsIso.inv_hom_id,
      injectivePushforwardHomEquiv_symm_id]

/-- A prescribed derived comparison of local replacements retains both original global chain
  adjoints. -/
lemma chainAdjoint_model_change (K : Complex X) (I J : Complex U) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (q : (restrict j).obj K ⟶ I) (r : (restrict j).obj K ⟶ J)
    (α : (toDerived U).obj I ⟶ (toDerived U).obj J)
    (h : (toDerived U).map q ≫ α = (toDerived U).map r) :
    (toDerived X).map ((restrictPushforwardComplexAdjunction j).homEquiv K I q) ≫
        (injectivePushforwardHomEquiv j I J b hJ iJ).symm α =
      (toDerived X).map ((restrictPushforwardComplexAdjunction j).homEquiv K J r) := by
  apply (pushforwardDerivedHomEquiv j K J b hJ iJ).injective
  rw [pushforwardDerivedHomEquiv_postcomp_derived j K I J a b hI iI hJ iJ,
    pushforwardDerivedHomEquiv_map, pushforwardDerivedHomEquiv_map,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact h

/-- Two genuine local injective replacements give an original global model isomorphism preserving
  both units. -/
lemma exists_pushforward_modelIso_of_local_replacements (K : Complex X) (I J : Complex U) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (q : (restrict j).obj K ⟶ I) (r : (restrict j).obj K ⟶ J) [QuasiIso q] [QuasiIso r] :
    ∃ e : (toDerived X).obj ((pushforwardComplex j).obj I) ≅
        (toDerived X).obj ((pushforwardComplex j).obj J),
      (toDerived X).map ((restrictPushforwardComplexAdjunction j).homEquiv K I q) ≫ e.hom =
        (toDerived X).map ((restrictPushforwardComplexAdjunction j).homEquiv K J r) ∧
      injectivePushforwardHomEquiv j I J b hJ iJ e.hom =
        inv ((toDerived U).map q) ≫ (toDerived U).map r := by
  let α := inv ((toDerived U).map q) ≫ (toDerived U).map r
  have : IsIso α := by dsimp [α]; infer_instance
  let f := (injectivePushforwardHomEquiv j I J b hJ iJ).symm α
  have : IsIso f := isIso_injectivePushforwardHomEquiv_symm j I J a b hI iI hJ iJ α
  refine ⟨asIso f, ?_, AddEquiv.apply_symm_apply _ _⟩
  exact chainAdjoint_model_change j K I J a b hI iI hJ iJ q r α (by simp [α])

end Quillen.PerfectComplexes
