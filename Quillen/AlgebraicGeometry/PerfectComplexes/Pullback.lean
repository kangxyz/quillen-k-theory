/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.Algebra.Homology.CochainComplex.Cycles
public import Aglib.Algebra.Homology.MappingCone.QuasiIso
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.KernelClosure
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Closure
public import Aglib.Algebra.Homology.MappingCone.NullHomotopy
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalQuasiIsoLifting
public import Quillen.AlgebraicGeometry.PerfectComplexes.Restriction
public import Quillen.Waldhausen.Functoriality.KMap
public import Aglib.AlgebraicGeometry.Modules.Complex.Pullback

/-!
# Actual arbitrary pullback of strict-perfect complexes

Termwise geometric pullback preserves bounded finite-locally-free complexes,
their actual short exact sequences, and their quasi-isomorphisms. The K-map is
induced directly by this geometric functor, satisfies identity and composition,
and agrees with open restriction, including inverse-image-open squares.

This concerns globally strict-perfect complexes. It does not assert that
underived pullback preserves arbitrary locally perfect complexes.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory.ExactCategory

open Quillen




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated CochainComplex
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- Arbitrary termwise pullback preserves genuine strict perfectness. -/
theorem strictPerfect_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : CochainComplex Y.Modules ℤ} (hK : strictPerfect Y K) :
    strictPerfect X ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj K) := by
  obtain ⟨⟨a, b, hb⟩, ht⟩ := hK
  refine ⟨⟨a, b, fun i hi => (Scheme.Modules.pullback f).map_isZero (hb i hi)⟩, fun i => ?_⟩
  let := ht i
  exact AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_pullback f (K.X i)

/-- Acyclic strict-perfect complexes remain acyclic under arbitrary pullback.
The proof uses actual finite-locally-free cycles and local exactness, rather
than assuming exactness of the ambient sheaf pullback. -/
theorem acyclic_pullback_of_strictPerfect {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : CochainComplex Y.Modules ℤ} (hK : strictPerfect Y K) (ha : K.Acyclic) :
    ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj K).Acyclic := by
  obtain ⟨⟨a, b, hb⟩, ht⟩ := hK
  apply _root_.CochainComplex.acyclic_map_of_cycle_sequences
  intro n
  let : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree Y (K.cycles (n + 1)) :=
    _root_.CochainComplex.cycles_mem (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree Y) K
      ht ha b
      (fun i hi => hb i (Or.inr hi)) (n + 1)
  let : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree Y
      (_root_.CochainComplex.cycleSequence K n).X₃ := by
    change AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree Y (K.cycles (n + 1))
    infer_instance
  exact AlgebraicGeometry.Scheme.Modules.shortExact_pullback f
    (_root_.CochainComplex.cycleSequence_shortExact K n (ha (n + 1)))

/-- Arbitrary pullback preserves quasi-isomorphisms between strict-perfect complexes. -/
theorem quasiIso_pullback_of_strictPerfect {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : CochainComplex Y.Modules ℤ} (hK : strictPerfect Y K) (hL : strictPerfect Y L)
    (s : K ⟶ L) [QuasiIso s] : QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map
      s) := by
  have hc := acyclic_pullback_of_strictPerfect f (strictPerfect_mappingCone hK hL s)
    (CochainComplex.mappingCone_acyclic_of_quasiIso s)
  apply CochainComplex.quasiIso_of_mappingCone_acyclic
  intro n
  exact (hc n).of_iso (mappingCone.mapHomologicalComplexIso s (Scheme.Modules.pullback f))

/-- Actual arbitrary pullback on globally strict-perfect complexes. -/
def strictPullback {X Y : Scheme.{u}} (f : X ⟶ Y) : StrictPerfect Y ⥤ StrictPerfect X :=
  (strictPerfect X).lift ((strictPerfect Y).ι ⋙ AlgebraicGeometry.Scheme.Modules.Complex.pullback f)
    (fun K => strictPerfect_pullback f K.property)

instance strictPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (strictPullback f).Additive := by unfold strictPullback; infer_instance

/-- Exactness on strict-perfect conflations follows from exactness on their
finite locally free terms, not from ambient left exactness. -/
def strictExactPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CategoryTheory.ExactCategory.ExactFunctor (strictExactStructure Y) (strictExactStructure X)
      where
  toFunctor := strictPullback f
  map_conflation S hS := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact
      (S.map (strictPerfect Y).ι)).mp hS n
    let : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree Y
        ((S.map (strictPerfect Y).ι).map
          (HomologicalComplex.eval Y.Modules (ComplexShape.up ℤ) n)).X₃ := S.X₃.property.2 n
    exact AlgebraicGeometry.Scheme.Modules.shortExact_pullback f h

instance pullbackComplex_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (AlgebraicGeometry.Scheme.Modules.Complex.pullback f) := by
  unfold AlgebraicGeometry.Scheme.Modules.Complex.pullback
  infer_instance

/-- Genuine arbitrary pullback is Waldhausen-exact on strict-perfect complexes. -/
theorem strictPullback_waldhausenExact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Waldhausen.IsExact (strictWaldhausen Y).cof (strictWaldhausen Y).weq
      (strictWaldhausen X).cof (strictWaldhausen X).weq (strictPullback f) where
  zero h := (strictPullback f).map_isZero h
  cofibration s hs := (strictExactPullback f).map_inflation s hs
  weak {K L} s hs := by
    let : QuasiIso s.hom := hs
    exact quasiIso_pullback_of_strictPerfect f K.property L.property s.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (strictPerfect X).ι
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure
      (CochainComplex Y.Modules ℤ))
      (strictPerfect Y) hi h).map (AlgebraicGeometry.Scheme.Modules.Complex.pullback f)

/-- The K-map is induced by the actual termwise strict-perfect pullback. -/
def strictKPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    StrictK Y n →* StrictK X n := Waldhausen.KMap (strictPullback_waldhausenExact f) n

/-- The geometric identity comparison lifts to strict-perfect complexes. -/
def strictPullbackIdIso (X : Scheme.{u}) :
    strictPullback (𝟙 X) ≅ 𝟭 (StrictPerfect X) :=
  Functor.fullyFaithfulCancelRight (strictPerfect X).ι
    (Functor.isoWhiskerLeft (strictPerfect X).ι (Scheme.Modules.Complex.pullbackIdIso X))

/-- The geometric composition comparison lifts to strict-perfect complexes. -/
def strictPullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    strictPullback (f ≫ g) ≅ strictPullback g ⋙ strictPullback f :=
  Functor.fullyFaithfulCancelRight (strictPerfect X).ι
    (Functor.isoWhiskerLeft (strictPerfect Z).ι (Scheme.Modules.Complex.pullbackCompIso f g))

/-- On an open immersion, actual termwise restriction is geometric pullback. -/
def restrictIsoPullbackComplex {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    restrict j ≅ AlgebraicGeometry.Scheme.Modules.Complex.pullback j :=
  NatIso.mapHomologicalComplex (Scheme.Modules.restrictFunctorIsoPullback j)
    (ComplexShape.up ℤ)

/-- Open restriction and arbitrary pullback agree on strict-perfect complexes. -/
def strictRestrictIsoPullback {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    strictRestrict j ≅ strictPullback j :=
  Functor.fullyFaithfulCancelRight (strictPerfect X).ι
    (Functor.isoWhiskerLeft (strictPerfect Y).ι (restrictIsoPullbackComplex j))

@[simp high]
theorem strictKPullback_id (X : Scheme.{u}) (n : ℕ) :
    strictKPullback (𝟙 X) n = MonoidHom.id (StrictK X n) :=
  (Waldhausen.KMap_eq_of_iso (strictPullback_waldhausenExact (𝟙 X))
    (Waldhausen.IsExact.id (strictWaldhausen X).cof (strictWaldhausen X).weq)
    (strictPullbackIdIso X) n).trans (Waldhausen.KMap_id _ n)

@[simp high]
theorem strictKPullback_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    strictKPullback (f ≫ g) n = (strictKPullback f n).comp (strictKPullback g n) :=
  (Waldhausen.KMap_eq_of_iso (strictPullback_waldhausenExact (f ≫ g))
    ((strictPullback_waldhausenExact g).comp (strictPullback_waldhausenExact f))
    (strictPullbackCompIso f g) n).trans
    (Quillen.Waldhausen.KMap_comp_KMap
      (strictPullback_waldhausenExact g) (strictPullback_waldhausenExact f) n).symm

/-- The original geometric open-restriction K-map is retained. -/
theorem strictKPullback_eq_restrict {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    strictKPullback j n = strictKRestrict j n :=
  Waldhausen.KMap_eq_of_iso (strictPullback_waldhausenExact j)
    (strictRestrict_waldhausenExact j) (strictRestrictIsoPullback j).symm n

/-- The inverse-image-open comparison retains actual strict-perfect pullback
and the original strict open-restriction functors. -/
def strictPullbackRestrictIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    strictPullback f ⋙ strictRestrict (f ⁻¹ᵁ U).ι ≅
      strictRestrict U.ι ⋙ strictPullback (f ∣_ U) :=
  Functor.fullyFaithfulCancelRight (strictPerfect (f ⁻¹ᵁ U).toScheme).ι
    (Functor.isoWhiskerLeft (strictPerfect Y).ι
      (AlgebraicGeometry.Scheme.Modules.Complex.pullbackRestrictIso f U))

/-- The genuine pullback/restriction square commutes on the original K-maps. -/
theorem strictKPullback_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (n : ℕ) :
    (strictKRestrict (f ⁻¹ᵁ U).ι n).comp (strictKPullback f n) =
      (strictKPullback (f ∣_ U) n).comp (strictKRestrict U.ι n) := by
  unfold strictKPullback strictKRestrict
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (strictPullbackRestrictIso f U) n

end Quillen.PerfectComplexes
