/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Representatives
public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction
public import Aglib.Algebra.Homology.HomotopyCategory.Adjunction
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenInjectiveModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedExtensionByZero
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
/-!
# Original derived Hom adjunction for injective direct-image targets

The actual restriction/direct-image sheaf adjunction acts degreewise. A genuine
lower term bound and injective terms imply K-injectivity both locally and after
ordinary direct image, since the original restriction is exact. The homotopy
adjunction therefore yields an additive Hom equivalence in the original ambient
derived categories for every original global source.

The equivalence agrees with original chain adjoints and with actual derived
restriction followed by the existing `pushforwardComplexRestrictIso` counit.
Arbitrary derived source denominators and actual target maps with independent
lower bounds retain their exact naturality equations. Every local derived arrow
has a global chain adjoint; a local weak chain input gives an adjoint weak after
restriction. No exactness of ordinary direct image, quasicoherence, upper bound,
or quasi-compactness is assumed.
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
/-- The standard derived model used in the original pushforward Hom adjunction. -/
local instance pushforwardHomStandardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules
  :=
  HasDerivedCategory.standard _
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original exact restriction and ordinary direct image form a genuine degreewise adjunction.
-/
def restrictPushforwardComplexAdjunction : restrict j ⊣ pushforwardComplex j :=
  (Scheme.Modules.restrictAdjunction j).mapHomologicalComplex (.up ℤ)

/-- Actual lower-bounded injective terms prove K-injectivity of the original target. -/
lemma isKInjective_of_lowerBounded_injective {Y : Scheme.{u}} (I : CochainComplex Y.Modules ℤ)
    (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n)) : I.IsKInjective := by
  have : I.IsStrictlyGE a := (_root_.CochainComplex.isStrictlyGE_iff I a).mpr hbound
  exact _root_.CochainComplex.isKInjective_of_injective I a

/-- Actual direct image of this target is K-injective, without exactness of ordinary direct image.
-/
lemma pushforwardComplex_isKInjective (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n)) :
    _root_.CochainComplex.IsKInjective ((pushforwardComplex j).obj I) := by
  apply isKInjective_of_lowerBounded_injective _ a
  · intro n hn
    exact (Scheme.Modules.pushforward j).map_isZero (hbound n hn)
  · intro n
    let := hinj n
    exact injective_pushforward j (I.X n)

/-- The original derived adjunction at an actual lower-bounded injective target.
The global source is unrestricted; ordinary direct image is not assumed exact. -/
def pushforwardDerivedHomEquiv (K : CochainComplex X.Modules ℤ) (I : CochainComplex U.Modules ℤ)
    (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n)) :
    ((DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((pushforwardComplex j).obj I)) ≃+
      ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ⟶
        (DerivedCategory.Q (C := U.Modules)).obj I) := by
  let := isKInjective_of_lowerBounded_injective I a hbound hinj
  let hJ := pushforwardComplex_isKInjective j I a hbound hinj
  let : _root_.CochainComplex.IsKInjective
      (((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℤ)).obj I) := hJ
  exact ((Scheme.Modules.restrictAdjunction j).cochainDerivedHomEquivOfKInjective K I).symm

/-- The equivalence maps original chain arrows to the original restricted chain adjoint. -/
@[simp]
lemma pushforwardDerivedHomEquiv_map (K : CochainComplex X.Modules ℤ)
    (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (f : K ⟶ (pushforwardComplex j).obj I) :
    pushforwardDerivedHomEquiv j K I a hbound hinj ((DerivedCategory.Q (C := X.Modules)).map f) =
      (DerivedCategory.Q (C := U.Modules)).map (((restrictPushforwardComplexAdjunction j).homEquiv K
        I).symm f) := by
  let := isKInjective_of_lowerBounded_injective I a hbound hinj
  let hJ := pushforwardComplex_isKInjective j I a hbound hinj
  let : _root_.CochainComplex.IsKInjective
      (((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℤ)).obj I) := hJ
  exact (Scheme.Modules.restrictAdjunction j).cochainDerivedHomEquivOfKInjective_symm_map K I f

/-- Every original derived arrow is transported by actual restriction followed by the original
  counit. -/
lemma pushforwardDerivedHomEquiv_eq (K : CochainComplex X.Modules ℤ)
    (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((pushforwardComplex j).obj I)) :
    pushforwardDerivedHomEquiv j K I a hbound hinj φ = restrictDerivedHom j φ ≫
      (DerivedCategory.Q (C := U.Modules)).map ((restrictPushforwardComplexAdjunction j).counit.app
        I) := by
  let := pushforwardComplex_isKInjective j I a hbound hinj
  obtain ⟨f, hf⟩ := _root_.CochainComplex.exists_chain_representative_of_isKInjective φ
  change (DerivedCategory.Q (C := X.Modules)).map f = φ at hf
  rw [← hf, pushforwardDerivedHomEquiv_map, restrictDerivedHom_map, ←
    CategoryTheory.Functor.map_comp]
  rfl

/-- Arbitrary original derived source maps satisfy the exact precomposition square. -/
lemma pushforwardDerivedHomEquiv_precomp {K K' : CochainComplex X.Modules ℤ}
    (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (α : (DerivedCategory.Q (C := X.Modules)).obj K' ⟶ (DerivedCategory.Q (C := X.Modules)).obj K)
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((pushforwardComplex j).obj I)) :
    pushforwardDerivedHomEquiv j K' I a hbound hinj (α ≫ φ) =
      restrictDerivedHom j α ≫ pushforwardDerivedHomEquiv j K I a hbound hinj φ := by
  rw [pushforwardDerivedHomEquiv_eq, pushforwardDerivedHomEquiv_eq,
    restrictDerivedHom_comp, Category.assoc]

/-- Inverse transport of an original local chain map is its actual global chain adjoint. -/
@[simp]
lemma pushforwardDerivedHomEquiv_symm_map (K : CochainComplex X.Modules ℤ)
    (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (g : (restrict j).obj K ⟶ I) :
    (pushforwardDerivedHomEquiv j K I a hbound hinj).symm
      ((DerivedCategory.Q (C := U.Modules)).map g) =
      (DerivedCategory.Q (C := X.Modules)).map ((restrictPushforwardComplexAdjunction j).homEquiv K
        I g) := by
  apply (pushforwardDerivedHomEquiv j K I a hbound hinj).injective
  rw [AddEquiv.apply_symm_apply, pushforwardDerivedHomEquiv_map, Equiv.symm_apply_apply]

end Quillen.PerfectComplexes

namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The degreewise adjunction counit is precisely the existing original restriction/direct-image
  isomorphism. -/
lemma restrictPushforwardComplexAdjunction_counit :
    (restrictPushforwardComplexAdjunction j).counit = (pushforwardComplexRestrictIso j).hom := by
  apply NatTrans.ext
  funext I
  ext n : 1
  change (Scheme.Modules.restrictAdjunction j).counit.app (I.X n) =
    (Scheme.Modules.restrictFunctorAdjCounitIso j).hom.app (I.X n) ≫ 𝟙 _
  rw [Category.comp_id]
  rfl

/-- The target-sensitive equivalence retains the already established original counit isomorphism. -/
lemma pushforwardDerivedHomEquiv_eq_original_counit (K : CochainComplex X.Modules ℤ)
    (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((pushforwardComplex j).obj I)) :
    pushforwardDerivedHomEquiv j K I a hbound hinj φ = restrictDerivedHom j φ ≫
      (DerivedCategory.Q (C := U.Modules)).map ((pushforwardComplexRestrictIso j).hom.app I) := by
  rw [pushforwardDerivedHomEquiv_eq, restrictPushforwardComplexAdjunction_counit]

/-- The inverse equivalence retains an arbitrary original derived denominator exactly. -/
lemma pushforwardDerivedHomEquiv_symm_precomp {K K' : CochainComplex X.Modules ℤ}
    (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (α : (DerivedCategory.Q (C := X.Modules)).obj K' ⟶ (DerivedCategory.Q (C := X.Modules)).obj K)
    (β : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj I) :
    (pushforwardDerivedHomEquiv j K' I a hbound hinj).symm (restrictDerivedHom j α ≫ β) =
      α ≫ (pushforwardDerivedHomEquiv j K I a hbound hinj).symm β := by
  apply (pushforwardDerivedHomEquiv j K' I a hbound hinj).injective
  rw [AddEquiv.apply_symm_apply, pushforwardDerivedHomEquiv_precomp, AddEquiv.apply_symm_apply]

/-- Actual target chain maps give derived naturality with independent original lower bounds. -/
lemma pushforwardDerivedHomEquiv_postcomp (K : CochainComplex X.Modules ℤ)
    (I J : CochainComplex U.Modules ℤ) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((pushforwardComplex j).obj I)) (f : I ⟶ J) :
    pushforwardDerivedHomEquiv j K J b hJ iJ (φ ≫ (DerivedCategory.Q (C := X.Modules)).map
      ((pushforwardComplex j).map f))
      =
      pushforwardDerivedHomEquiv j K I a hI iI φ ≫ (DerivedCategory.Q (C := U.Modules)).map f := by
  rw [pushforwardDerivedHomEquiv_eq, pushforwardDerivedHomEquiv_eq,
    restrictDerivedHom_comp, restrictDerivedHom_map, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  have h := (restrictPushforwardComplexAdjunction j).counit.naturality f
  change (restrict j).map ((pushforwardComplex j).map f) ≫
    (restrictPushforwardComplexAdjunction j).counit.app J =
      (restrictPushforwardComplexAdjunction j).counit.app I ≫ f at h
  rw [h, CategoryTheory.Functor.map_comp, Category.assoc]

/-- The actual counit gives the original quasi-isomorphism after restriction of its chain adjoint.
-/
lemma quasiIso_restrict_chain_adjoint {K : CochainComplex X.Modules ℤ}
    {I : CochainComplex U.Modules ℤ}
    (q : (restrict j).obj K ⟶ I) [QuasiIso q] :
    QuasiIso ((restrict j).map ((restrictPushforwardComplexAdjunction j).homEquiv K I q)) := by
  have hc : IsIso ((restrictPushforwardComplexAdjunction j).counit.app I) := by
    rw [restrictPushforwardComplexAdjunction_counit]
    infer_instance
  apply (quasiIso_iff_comp_right _ ((restrictPushforwardComplexAdjunction j).counit.app I)).mp
  change QuasiIso (((restrictPushforwardComplexAdjunction j).homEquiv K I).symm
    ((restrictPushforwardComplexAdjunction j).homEquiv K I q))
  rw [Equiv.symm_apply_apply]
  infer_instance

/-- Every original local derived map into the actual injective target has a genuine global chain
  adjoint. -/
lemma exists_pushforward_chain_adjoint (K : CochainComplex X.Modules ℤ)
    (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (α : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj I) :
    ∃ f : K ⟶ (pushforwardComplex j).obj I,
      pushforwardDerivedHomEquiv j K I a hbound hinj ((DerivedCategory.Q (C := X.Modules)).map f)
        = α := by
  let : HasDerivedCategory.{u+1} U.Modules := HasDerivedCategory.standard _
  let := isKInjective_of_lowerBounded_injective I a hbound hinj
  obtain ⟨q, hq⟩ := _root_.CochainComplex.exists_chain_representative_of_isKInjective α
  refine ⟨(restrictPushforwardComplexAdjunction j).homEquiv K I q, ?_⟩
  rw [pushforwardDerivedHomEquiv_map, Equiv.symm_apply_apply]
  exact hq

end Quillen.PerfectComplexes
