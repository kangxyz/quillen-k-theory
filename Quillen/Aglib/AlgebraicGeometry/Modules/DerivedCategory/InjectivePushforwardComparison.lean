/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.InjectivePushforwardAdjunction
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Map
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
/-! # Original injective-target direct-image model changes

The genuine target-sensitive Hom adjunction and the original restriction/direct-
image counit give an additive Hom equivalence. Its inverse is the actual action
on K-injective-target homotopy classes. The source is unrestricted, while the
target is genuinely lower-bounded and termwise injective.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes
/-- The standard derived model used for the original injective model comparison. -/
local instance modelChangeStandardDerived (Y : Scheme.{u}) : HasDerivedCategory.{u+1} Y.Modules :=
  HasDerivedCategory.standard _
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Original direct-image Hom equivalence with an unrestricted local source and actual injective
  target. -/
def injectivePushforwardHomEquiv (I J : CochainComplex U.Modules ℤ) (b : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n)) :
    ((DerivedCategory.Q (C := X.Modules)).obj ((pushforwardComplex j).obj I) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj ((pushforwardComplex j).obj J)) ≃+
      ((DerivedCategory.Q (C := U.Modules)).obj I ⟶ (DerivedCategory.Q (C := U.Modules)).obj J) :=
  { toFun α := (DerivedCategory.Q (C := U.Modules)).map
      ((pushforwardComplexRestrictIso j).inv.app I) ≫
      pushforwardDerivedHomEquiv j ((pushforwardComplex j).obj I) J b hJ iJ α
    invFun β := (pushforwardDerivedHomEquiv j ((pushforwardComplex j).obj I) J b hJ iJ).symm
      ((DerivedCategory.Q (C := U.Modules)).map ((pushforwardComplexRestrictIso j).hom.app I) ≫ β)
    left_inv α := by
      apply (pushforwardDerivedHomEquiv j ((pushforwardComplex j).obj I) J b hJ iJ).injective
      simp only [AddEquiv.apply_symm_apply, ← Category.assoc,
        ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
      erw [(DerivedCategory.Q (C := U.Modules)).map_id]
      exact Category.id_comp _
    right_inv β := by
      simp only [AddEquiv.apply_symm_apply, ← Category.assoc,
        ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
      erw [(DerivedCategory.Q (C := U.Modules)).map_id]
      exact Category.id_comp _
    map_add' α β := by simp [Preadditive.comp_add] }

/-- The equivalence is actual derived restriction conjugated by the original counits. -/
lemma injectivePushforwardHomEquiv_eq (I J : CochainComplex U.Modules ℤ) (b : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (α : (DerivedCategory.Q (C := X.Modules)).obj ((pushforwardComplex j).obj I) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj ((pushforwardComplex j).obj J)) :
    injectivePushforwardHomEquiv j I J b hJ iJ α =
      (DerivedCategory.Q (C := U.Modules)).map ((pushforwardComplexRestrictIso j).inv.app I) ≫
        restrictDerivedHom j α ≫
          (DerivedCategory.Q (C := U.Modules)).map
            ((pushforwardComplexRestrictIso j).hom.app J) := by
  exact congrArg (fun t => (DerivedCategory.Q (C := U.Modules)).map
    ((pushforwardComplexRestrictIso j).inv.app I) ≫ t)
    (pushforwardDerivedHomEquiv_eq_original_counit j ((pushforwardComplex j).obj I) J b hJ iJ α)

/-- An actual pushed-forward chain map is sent to the original local derived map. -/
@[simp]
lemma injectivePushforwardHomEquiv_map (I J : CochainComplex U.Modules ℤ) (b : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n)) (f : I ⟶ J) :
    injectivePushforwardHomEquiv j I J b hJ iJ
      ((DerivedCategory.Q (C := X.Modules)).map ((pushforwardComplex j).map f)) =
        (DerivedCategory.Q (C := U.Modules)).map f := by
  rw [injectivePushforwardHomEquiv_eq, restrictDerivedHom_map,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  have h := (pushforwardComplexRestrictIso j).hom.naturality f
  change (restrict j).map ((pushforwardComplex j).map f) ≫
    (pushforwardComplexRestrictIso j).hom.app J =
      (pushforwardComplexRestrictIso j).hom.app I ≫ f at h
  rw [h, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- The inverse equivalence agrees with the genuine homotopy-class action of ordinary direct image.
-/
lemma injectivePushforwardHomEquiv_symm_eq (I J : CochainComplex U.Modules ℤ) (b : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (α : (DerivedCategory.Q (C := U.Modules)).obj I ⟶ (DerivedCategory.Q (C := U.Modules)).obj J) :
    (injectivePushforwardHomEquiv j I J b hJ iJ).symm α =
      letI := isKInjective_of_lowerBounded_injective J b hJ iJ
      _root_.CochainComplex.mapDerivedHomOfKInjective (Scheme.Modules.pushforward j) I J α := by
  let := isKInjective_of_lowerBounded_injective J b hJ iJ
  obtain ⟨f, hf⟩ := _root_.CochainComplex.exists_chain_representative_of_isKInjective α
  change (DerivedCategory.Q (C := U.Modules)).map f = α at hf
  rw [← hf]
  have hm := _root_.CochainComplex.mapDerivedHomOfKInjective_map (Scheme.Modules.pushforward j) I J
    f
  change _root_.CochainComplex.mapDerivedHomOfKInjective (Scheme.Modules.pushforward j) I J
    ((DerivedCategory.Q (C := U.Modules)).map f) = (DerivedCategory.Q (C := X.Modules)).map
      ((pushforwardComplex j).map f) at hm
  rw [hm]
  apply (injectivePushforwardHomEquiv j I J b hJ iJ).injective
  rw [AddEquiv.apply_symm_apply, injectivePushforwardHomEquiv_map]

/-- The inverse comparison preserves the original direct image of every chain map. -/
@[simp]
lemma injectivePushforwardHomEquiv_symm_map (I J : CochainComplex U.Modules ℤ) (b : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n)) (f : I ⟶ J) :
    (injectivePushforwardHomEquiv j I J b hJ iJ).symm ((DerivedCategory.Q (C := U.Modules)).map f) =
      (DerivedCategory.Q (C := X.Modules)).map ((pushforwardComplex j).map f) := by
  apply (injectivePushforwardHomEquiv j I J b hJ iJ).injective
  rw [AddEquiv.apply_symm_apply, injectivePushforwardHomEquiv_map]

/-- Original Hom transposition is natural under every genuine derived target-model map. -/
lemma pushforwardDerivedHomEquiv_postcomp_derived (K : CochainComplex X.Modules ℤ)
    (I J : CochainComplex U.Modules ℤ) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((pushforwardComplex j).obj I))
    (β : (DerivedCategory.Q (C := U.Modules)).obj I ⟶ (DerivedCategory.Q (C := U.Modules)).obj J) :
    pushforwardDerivedHomEquiv j K J b hJ iJ
        (φ ≫ (injectivePushforwardHomEquiv j I J b hJ iJ).symm β) =
      pushforwardDerivedHomEquiv j K I a hI iI φ ≫ β := by
  let := isKInjective_of_lowerBounded_injective J b hJ iJ
  obtain ⟨f, hf⟩ := _root_.CochainComplex.exists_chain_representative_of_isKInjective β
  change (DerivedCategory.Q (C := U.Modules)).map f = β at hf
  rw [← hf, injectivePushforwardHomEquiv_symm_map]
  exact pushforwardDerivedHomEquiv_postcomp j K I J a b hI iI hJ iJ φ f

/-- Direct-image model change retains actual original derived composition. -/
lemma injectivePushforwardHomEquiv_symm_comp (I J L : CochainComplex U.Modules ℤ) (b c : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (hL : ∀ n, n < c → IsZero (L.X n)) (iL : ∀ n, Injective (L.X n))
    (α : (DerivedCategory.Q (C := U.Modules)).obj I ⟶ (DerivedCategory.Q (C := U.Modules)).obj J)
    (β : (DerivedCategory.Q (C := U.Modules)).obj J ⟶ (DerivedCategory.Q (C := U.Modules)).obj L) :
    (injectivePushforwardHomEquiv j I L c hL iL).symm (α ≫ β) =
      (injectivePushforwardHomEquiv j I J b hJ iJ).symm α ≫
        (injectivePushforwardHomEquiv j J L c hL iL).symm β := by
  let := isKInjective_of_lowerBounded_injective J b hJ iJ
  let := isKInjective_of_lowerBounded_injective L c hL iL
  obtain ⟨f, hf⟩ := _root_.CochainComplex.exists_chain_representative_of_isKInjective α
  obtain ⟨g, hg⟩ := _root_.CochainComplex.exists_chain_representative_of_isKInjective β
  change (DerivedCategory.Q (C := U.Modules)).map f = α at hf
  change (DerivedCategory.Q (C := U.Modules)).map g = β at hg
  rw [← hf, ← hg, ← CategoryTheory.Functor.map_comp,
    injectivePushforwardHomEquiv_symm_map, injectivePushforwardHomEquiv_symm_map,
    injectivePushforwardHomEquiv_symm_map, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]

/-- The actual original identity is unchanged by injective-model direct image. -/
@[simp]
lemma injectivePushforwardHomEquiv_symm_id (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n)) :
    (injectivePushforwardHomEquiv j I I a hI iI).symm (𝟙 _) = 𝟙 _ := by
  simpa using injectivePushforwardHomEquiv_symm_map j I I a hI iI (𝟙 I)

/-- Genuine derived isomorphisms of injective models induce genuine original direct-image
  isomorphisms. -/
lemma isIso_injectivePushforwardHomEquiv_symm (I J : CochainComplex U.Modules ℤ) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (α : (DerivedCategory.Q (C := U.Modules)).obj I ⟶ (DerivedCategory.Q (C := U.Modules)).obj J)
      [IsIso α] :
    IsIso ((injectivePushforwardHomEquiv j I J b hJ iJ).symm α) := by
  refine ⟨⟨(injectivePushforwardHomEquiv j J I a hI iI).symm (inv α), ?_, ?_⟩⟩
  · rw [← injectivePushforwardHomEquiv_symm_comp, IsIso.hom_inv_id,
      injectivePushforwardHomEquiv_symm_id]
  · rw [← injectivePushforwardHomEquiv_symm_comp, IsIso.inv_hom_id,
      injectivePushforwardHomEquiv_symm_id]

/-- A prescribed derived comparison of local replacements retains both original global chain
  adjoints. -/
lemma chainAdjoint_model_change (K : CochainComplex X.Modules ℤ) (I J : CochainComplex U.Modules ℤ)
    (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (q : (restrict j).obj K ⟶ I) (r : (restrict j).obj K ⟶ J)
    (α : (DerivedCategory.Q (C := U.Modules)).obj I ⟶ (DerivedCategory.Q (C := U.Modules)).obj J)
    (h : (DerivedCategory.Q (C := U.Modules)).map q ≫ α =
      (DerivedCategory.Q (C := U.Modules)).map r) :
    (DerivedCategory.Q (C := X.Modules)).map ((restrictPushforwardComplexAdjunction j).homEquiv K I
      q) ≫
        (injectivePushforwardHomEquiv j I J b hJ iJ).symm α =
      (DerivedCategory.Q (C := X.Modules)).map ((restrictPushforwardComplexAdjunction j).homEquiv K
        J r) := by
  apply (pushforwardDerivedHomEquiv j K J b hJ iJ).injective
  rw [pushforwardDerivedHomEquiv_postcomp_derived j K I J a b hI iI hJ iJ,
    pushforwardDerivedHomEquiv_map, pushforwardDerivedHomEquiv_map,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact h

/-- Two genuine local injective replacements give an original global model isomorphism preserving
  both units. -/
lemma exists_pushforward_modelIso_of_local_replacements (K : CochainComplex X.Modules ℤ)
    (I J : CochainComplex U.Modules ℤ) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (q : (restrict j).obj K ⟶ I) (r : (restrict j).obj K ⟶ J) [QuasiIso q] [QuasiIso r] :
    ∃ e : (DerivedCategory.Q (C := X.Modules)).obj ((pushforwardComplex j).obj I) ≅
        (DerivedCategory.Q (C := X.Modules)).obj ((pushforwardComplex j).obj J),
      (DerivedCategory.Q (C := X.Modules)).map ((restrictPushforwardComplexAdjunction j).homEquiv K
        I q) ≫ e.hom =
        (DerivedCategory.Q (C := X.Modules)).map ((restrictPushforwardComplexAdjunction j).homEquiv
          K J r) ∧
      injectivePushforwardHomEquiv j I J b hJ iJ e.hom =
        inv ((DerivedCategory.Q (C := U.Modules)).map q) ≫
          (DerivedCategory.Q (C := U.Modules)).map r := by
  let α := inv ((DerivedCategory.Q (C := U.Modules)).map q) ≫
    (DerivedCategory.Q (C := U.Modules)).map r
  have : IsIso α := by dsimp [α]; infer_instance
  let f := (injectivePushforwardHomEquiv j I J b hJ iJ).symm α
  have : IsIso f := isIso_injectivePushforwardHomEquiv_symm j I J a b hI iI hJ iJ α
  refine ⟨asIso f, ?_, AddEquiv.apply_symm_apply _ _⟩
  exact chainAdjoint_model_change j K I J a b hI iI hJ iJ q r α (by simp [α])

end Quillen.PerfectComplexes
