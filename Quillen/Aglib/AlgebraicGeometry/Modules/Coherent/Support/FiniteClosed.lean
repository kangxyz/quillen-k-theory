/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.ExtensionByZero
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Quillen.Aglib.CategoryTheory.Pi.FiniteStages
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Coherent sheaves with finite closed support

For a locally Noetherian scheme and a finite set `S` of closed points,
`finiteSupportEquivalence` identifies actual coherent sheaves supported in `S`
with the finite product of the actual singleton-supported coherent categories.
Its forward functor is the finite sum of the original singleton inclusions.
Both directions are exact. The support categories are kernels of actual open
restriction, and `closedSupportProperty_iff` retains ordinary stalk support.

For each `i` in `S`, restrict to the complement of the other points and extend
by zero. The finite sum of the original adjunction counits is stalkwise an
isomorphism. Each component is therefore an actual retract of the original
sheaf, so finite-colimit closure proves its coherence. Orthogonality of
singleton supports proves full faithfulness of the original summation functor.
The empty set and arbitrary zero objects outside a singleton are included.

`singletonSumIso` retains each original singleton inclusion. The chosen inverse
has exact evaluations, with `pointInclusionEvaluationSelfIso` and
`pointInclusionEvaluationOtherIso` giving their original coordinate equations.
No residue-field or categorical residue-vector-space identification is used.

Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Coherent.Support.FiniteClosed`.
Current consumer: Quillen's finite closed-point coherent support assembly for
surface second-support K1. Small-model transport, the union over finite sets,
and K-theory assembly are separate downstream constructions.
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

namespace AlgebraicGeometry.Scheme.Modules.Coherent.FiniteClosedSupport

/-- Outside ordinary stalk support the actual module stalk is zero. -/
lemma moduleStalk_isZero_of_not_mem_support {X : Scheme.{u}} (M : X.Modules) (x : X)
    (h : x ∉ support M) : IsZero ((moduleStalk X x).obj M) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map_injective
  exact (IsZero.iff_id_eq_zero _).1 (Classical.not_not.mp h)

/-- A zero module stalk gives absence from ordinary stalk support. -/
lemma not_mem_support_of_moduleStalk_isZero {X : Scheme.{u}} (M : X.Modules) (x : X)
    (h : IsZero ((moduleStalk X x).obj M)) : x ∉ support M := by
  exact fun hx => hx ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map_isZero h)

/-- Inside an open, the original extension-by-zero counit is a stalk isomorphism. -/
lemma counitModuleStalk_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (y : U) :
    IsIso ((moduleStalk X (j y)).map
      ((extensionByZeroRestrictAdjunction j).counit.app M)) := by
  apply (NatIso.isIso_map_iff (restrictModuleStalkIso j y) _).1
  change IsIso ((ModuleCat.restrictScalars (j.stalkMap y).hom).map
    ((moduleStalk U y).map ((Scheme.Modules.restrictFunctor j).map
      ((extensionByZeroRestrictAdjunction j).counit.app M))))
  infer_instance

/-- A finite set of closed points is closed, without a global T1 assumption. -/
lemma closed_finset (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) : IsClosed (S : Set X) := by
  convert isClosed_biUnion_finset (s := S) (f := fun x => ({x} : Set X)) hS using 1
  ext x
  simp

/-- The complement of all points of the finite set except the selected point. -/
def isolatingOpen (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) : X.Opens :=
  ⟨(↑(S.erase i.val) : Set X)ᶜ,
    (closed_finset X (S.erase i.val) (fun x hx => hS x (Finset.mem_of_mem_erase hx))).isOpen_compl⟩

@[simp] lemma mem_isolatingOpen (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) (x : X) :
    x ∈ isolatingOpen X S hS i ↔ x ∉ S ∨ x = i.val := by
  change x ∉ S.erase i.val ↔ _
  simp only [Finset.mem_erase, not_and_or, not_not, or_comm]

/-- Actual open restriction followed by genuine extension by zero. -/
def componentFunctor (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) : X.Modules ⥤ X.Modules :=
  Scheme.Modules.restrictFunctor (isolatingOpen X S hS i).ι ⋙
    extensionByZero (isolatingOpen X S hS i).ι

/-- The original extension-by-zero adjunction counit for the selected component. -/
def componentCounit (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) :
    componentFunctor X S hS i ⟶ 𝟭 X.Modules :=
  (extensionByZeroRestrictAdjunction (isolatingOpen X S hS i).ι).counit

/-- The selected component has its original stalk on its isolating open. -/
lemma componentCounit_stalk_isIso (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) (M : X.Modules) (x : X)
    (hx : x ∈ isolatingOpen X S hS i) :
    IsIso ((moduleStalk X x).map ((componentCounit X S hS i).app M)) :=
  counitModuleStalk_isIso (isolatingOpen X S hS i).ι M ⟨x, hx⟩

/-- The selected component has zero stalks outside its isolating open. -/
lemma component_stalk_isZero_of_not_mem (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) (M : X.Modules) (x : X)
    (hx : x ∉ isolatingOpen X S hS i) :
    IsZero ((moduleStalk X x).obj ((componentFunctor X S hS i).obj M)) := by
  apply isZero_extensionByZero_stalk_of_not_mem (isolatingOpen X S hS i).ι x
  rintro ⟨y, rfl⟩
  exact hx y.property

/-- For a sheaf supported in the finite set, each component is supported at its point. -/
lemma component_support_subset (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) (M : X.Modules)
    (hM : support M ⊆ (S : Set X)) :
    support ((componentFunctor X S hS i).obj M) ⊆ {i.val} := by
  intro x hx
  by_contra hxi
  have hxi' : x ≠ i.val := hxi
  by_cases hU : x ∈ isolatingOpen X S hS i
  · have hnotS : x ∉ S := ((mem_isolatingOpen X S hS i x).1 hU).resolve_right hxi'
    have hzero := moduleStalk_isZero_of_not_mem_support M x (fun h => hnotS (hM h))
    let := componentCounit_stalk_isIso X S hS i M x hU
    exact (not_mem_support_of_moduleStalk_isZero _ x
      (hzero.of_iso (asIso ((moduleStalk X x).map
        ((componentCounit X S hS i).app M))))) hx
  · exact (not_mem_support_of_moduleStalk_isZero _ x
      (component_stalk_isZero_of_not_mem X S hS i M x hU)) hx

/-- A biproduct map is invertible when one component is invertible and the others are zero. -/
lemma isIso_biproduct_desc_of_single {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {I : Type*} (A : I → C) [HasBiproduct A] {Y : C} (f : ∀ i, A i ⟶ Y)
    (i : I) [IsIso (f i)] (h : ∀ j, j ≠ i → IsZero (A j)) :
    IsIso (biproduct.desc f) := by
  refine ⟨⟨inv (f i) ≫ biproduct.ι A i, ?_, ?_⟩⟩
  · apply biproduct.hom_ext'
    intro j
    by_cases hj : j = i
    · subst j
      simp
    · exact (h j hj).eq_of_src _ _
  · simp

/-- The actual finite sum of the original component counits. -/
def componentSumMap (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (M : X.Modules) :
    (⨁ fun i : S => (componentFunctor X S hS i).obj M) ⟶ M :=
  biproduct.desc (fun i => (componentCounit X S hS i).app M)

/-- The original counit sum reconstructs every sheaf with the given finite closed support. -/
lemma componentSumMap_isIso (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (M : X.Modules)
    (hM : support M ⊆ (S : Set X)) : IsIso (componentSumMap X S hS M) := by
  apply isIso_of_moduleStalk
  intro x
  let T := moduleStalk X x
  let := preservesBiproduct_of_preservesProduct T
    (f := fun i : S => (componentFunctor X S hS i).obj M)
  change IsIso (T.map (biproduct.desc (fun i : S => (componentCounit X S hS i).app M)))
  rw [← biproduct.mapBiproduct_hom_desc]
  have hleft : IsIso ((T.mapBiproduct (fun i : S =>
      (componentFunctor X S hS i).obj M)).hom) := inferInstance
  by_cases hx : x ∈ S
  · let i : S := ⟨x, hx⟩
    have hi : x ∈ isolatingOpen X S hS i := (mem_isolatingOpen X S hS i x).2 (Or.inr rfl)
    let := componentCounit_stalk_isIso X S hS i M x hi
    have hz (j : S) (hj : j ≠ i) :
        IsZero (T.obj ((componentFunctor X S hS j).obj M)) := by
      apply component_stalk_isZero_of_not_mem X S hS j M x
      intro hU
      rcases (mem_isolatingOpen X S hS j x).1 hU with h | h
      · exact h hx
      · exact hj (Subtype.ext h.symm)
    have hd := isIso_biproduct_desc_of_single _
      (fun j : S => T.map ((componentCounit X S hS j).app M)) i hz
    exact IsIso.comp_isIso' hleft hd
  · have hzero : IsZero (T.obj M) :=
      moduleStalk_isZero_of_not_mem_support M x (fun h => hx (hM h))
    have hz (i : S) : IsZero (T.obj ((componentFunctor X S hS i).obj M)) :=
      moduleStalk_isZero_of_not_mem_support _ x
        (fun h => hx ((Set.mem_singleton_iff.mp (component_support_subset X S hS i M hM h)) ▸
          i.property))
    have hsum : IsZero (⨁ fun i : S => T.obj ((componentFunctor X S hS i).obj M)) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply biproduct.hom_ext'
      intro i
      exact (hz i).eq_of_src _ _
    have hd := hsum.isIso hzero
      (biproduct.desc (fun i : S => T.map ((componentCounit X S hS i).app M)))
    exact IsIso.comp_isIso' hleft hd

/-- Each component is an actual retract, using the inverse counit sum and its projection. -/
def componentRetract (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) (M : X.Modules)
    (hM : support M ⊆ (S : Set X)) :
    Retract ((componentFunctor X S hS i).obj M) M := by
  let := componentSumMap_isIso X S hS M hM
  exact {
    i := (componentCounit X S hS i).app M
    r := inv (componentSumMap X S hS M) ≫
      biproduct.π (fun i : S => (componentFunctor X S hS i).obj M) i
    retract := by
      have hi : biproduct.ι (fun i : S => (componentFunctor X S hS i).obj M) i ≫
          componentSumMap X S hS M = (componentCounit X S hS i).app M :=
        biproduct.ι_desc _ i
      rw [← hi, Category.assoc, IsIso.hom_inv_id_assoc, biproduct.ι_π_self] }

/-- Actual retract closure makes the supported components of a coherent sheaf coherent. -/
lemma component_coherent (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) (M : FiniteTypeSheaves X)
    (hM : support M.obj ⊆ (S : Set X)) :
    affineLocallyFiniteType X ((componentFunctor X S hS i).obj M.obj) :=
  (affineLocallyFiniteType X).prop_of_retract (componentRetract X S hS i M.obj hM) M.property

/-- A sheaf supported inside an open is reconstructed by the original extension counit. -/
lemma counit_isIso_of_support_subset {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (hM : support M ⊆ Set.range j) :
    IsIso ((extensionByZeroRestrictAdjunction j).counit.app M) := by
  apply isIso_of_moduleStalk
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    exact counitModuleStalk_isIso j M y
  · exact (isZero_extensionByZero_stalk_of_not_mem j x hx _).isIso
      (moduleStalk_isZero_of_not_mem_support M x (fun h => hx (hM h))) _

/-- Morphisms between distinct singleton supports vanish, using the actual open adjunction. -/
lemma hom_eq_zero_of_singleton_support {X : Scheme.{u}} (x y : X)
    (hy : IsClosed ({y} : Set X)) (hxy : x ≠ y) {M N : X.Modules}
    (hM : support M ⊆ {x}) (hN : support N ⊆ {y}) (f : M ⟶ N) : f = 0 := by
  let U : X.Opens := ⟨({y} : Set X)ᶜ, hy.isOpen_compl⟩
  let a := extensionByZeroRestrictAdjunction U.ι
  have hMU : support M ⊆ Set.range U.ι := by
    intro z hz
    have hz' : z = x := Set.mem_singleton_iff.mp (hM hz)
    subst z
    exact ⟨⟨x, hxy⟩, rfl⟩
  let := counit_isIso_of_support_subset U.ι M hMU
  have hNU : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj N) := by
    apply (supportedAway_iff_stalks U.ι N).2
    intro z
    exact Classical.not_not.mp (fun hz => z.property (hN hz))
  apply (cancel_epi (a.counit.app M)).1
  apply (a.homEquiv ((Scheme.Modules.restrictFunctor U.ι).obj M) N).injective
  exact hNU.eq_of_tgt _ _

/-- The actual open complement of a specified closed subset. -/
def complementOpen (X : Scheme.{u}) (T : Set X) (hT : IsClosed T) : X.Opens :=
  ⟨Tᶜ, hT.isOpen_compl⟩

/-- Coherent sheaves vanishing on the actual open complement of a closed subset. -/
def closedSupportProperty (X : Scheme.{u}) (T : Set X) (hT : IsClosed T) :
    ObjectProperty (FiniteTypeSheaves X) :=
  finiteTypeSheavesSupportedAway (complementOpen X T hT).ι

/-- The restriction-kernel predicate is precisely containment of ordinary stalk support. -/
lemma closedSupportProperty_iff (X : Scheme.{u}) (T : Set X) (hT : IsClosed T)
    (M : FiniteTypeSheaves X) : closedSupportProperty X T hT M ↔ support M.obj ⊆ T := by
  rw [closedSupportProperty, finiteTypeSheavesSupportedAway_iff_support_subset]
  have hr : Set.range (complementOpen X T hT).ι = Tᶜ := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rw [hr, compl_compl]

instance closedSupportProperty_serre (X : Scheme.{u}) [IsLocallyNoetherian X]
    (T : Set X) (hT : IsClosed T) : (closedSupportProperty X T hT).IsSerreClass := by
  dsimp [closedSupportProperty]
  infer_instance

/-- Actual finite-type quasicoherent sheaves with the specified closed support. -/
abbrev ClosedSupportCategory (X : Scheme.{u}) (T : Set X) (hT : IsClosed T) :=
  (closedSupportProperty X T hT).FullSubcategory

/-- Actual coherent sheaves supported in a fixed finite set of closed points. -/
abbrev FiniteSupportCategory (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) :=
  ClosedSupportCategory X (S : Set X) (closed_finset X S hS)

/-- Actual coherent sheaves supported at one of the specified closed points. -/
abbrev PointSupportCategory (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) :=
  ClosedSupportCategory X {i.val} (hS i.val i.property)

/-- The original full inclusion of a singleton support into the finite support category. -/
def pointInclusion (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) :
    PointSupportCategory X S hS i ⥤ FiniteSupportCategory X S hS :=
  ObjectProperty.ιOfLE (fun M hM =>
    (closedSupportProperty_iff X _ _ M).2 (fun x hx => by
      have hx' := Set.mem_singleton_iff.mp ((closedSupportProperty_iff X _ _ M).1 hM hx)
      change x ∈ S
      simpa only [hx'] using i.property))

instance pointInclusion_full (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) :
    (pointInclusion X S hS i).Full := by
  dsimp [pointInclusion]
  infer_instance

instance pointInclusion_faithful (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) :
    (pointInclusion X S hS i).Faithful := by
  dsimp [pointInclusion]
  infer_instance

instance pointInclusion_additive (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) :
    (pointInclusion X S hS i).Additive where
  map_add := by intros; rfl

/-- Distinct original singleton inclusions have only zero cross-coordinate morphisms. -/
lemma pointInclusion_hom_eq_zero (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i j : S) (hij : i ≠ j)
    (A : PointSupportCategory X S hS i) (B : PointSupportCategory X S hS j)
    (f : (pointInclusion X S hS i).obj A ⟶ (pointInclusion X S hS j).obj B) : f = 0 := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact hom_eq_zero_of_singleton_support i.val j.val (hS j.val j.property)
    (fun h => hij (Subtype.ext h))
    ((closedSupportProperty_iff X _ _ A.obj).1 A.property)
    ((closedSupportProperty_iff X _ _ B.obj).1 B.property) f.hom.hom

/-- Finite reconstruction by the actual biproduct of original singleton inclusions. -/
def sumFunctor (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) :
    (∀ i : S, PointSupportCategory X S hS i) ⥤ FiniteSupportCategory X S hS where
  obj A := ⨁ fun i : S => (pointInclusion X S hS i).obj (A i)
  map f := biproduct.map (fun i => (pointInclusion X S hS i).map (f i))
  map_id A := by
    apply biproduct.hom_ext
    intro i
    simp
  map_comp f g := by
    apply biproduct.hom_ext
    intro i
    simp [Category.assoc]

instance sumFunctor_full (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) : (sumFunctor X S hS).Full where
  map_surjective {A B} f := by
    let g : A ⟶ B := fun i => (pointInclusion X S hS i).preimage
      (biproduct.ι (fun i : S => (pointInclusion X S hS i).obj (A i)) i ≫ f ≫
        biproduct.π (fun i : S => (pointInclusion X S hS i).obj (B i)) i)
    refine ⟨g, ?_⟩
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    by_cases hij : i = j
    · subst j
      simp [sumFunctor, g]
    · have hzero := pointInclusion_hom_eq_zero X S hS i j hij (A i) (B j)
        (biproduct.ι (fun i : S => (pointInclusion X S hS i).obj (A i)) i ≫ f ≫
          biproduct.π (fun i : S => (pointInclusion X S hS i).obj (B i)) j)
      simpa [sumFunctor, hij] using hzero.symm

instance sumFunctor_faithful (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) : (sumFunctor X S hS).Faithful where
  map_injective {A B} f g h := by
    funext i
    apply (pointInclusion X S hS i).map_injective
    have hi := congrArg (fun k =>
      biproduct.ι (fun i : S => (pointInclusion X S hS i).obj (A i)) i ≫ k ≫
        biproduct.π (fun i : S => (pointInclusion X S hS i).obj (B i)) i) h
    simpa [sumFunctor] using hi

/-- The original fully faithful realization as actual module sheaves. -/
abbrev finiteSupportToModules (X : Scheme.{u}) (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) : FiniteSupportCategory X S hS ⥤ X.Modules :=
  (closedSupportProperty X (S : Set X) (closed_finset X S hS)).ι ⋙ finiteTypeSheavesToModules X

instance sumFunctor_essSurj (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) : (sumFunctor X S hS).EssSurj where
  mem_essImage M := by
    have hM := (closedSupportProperty_iff X _ _ M.obj).1 M.property
    let A : ∀ i : S, PointSupportCategory X S hS i := fun i =>
      ⟨⟨(componentFunctor X S hS i).obj M.obj.obj,
        component_coherent X S hS i M.obj hM⟩,
        (closedSupportProperty_iff X _ _ _).2
          (component_support_subset X S hS i M.obj.obj hM)⟩
    let F := finiteSupportToModules X S hS
    let family := fun i : S => (pointInclusion X S hS i).obj (A i)
    let := ObjectProperty.inclusion_preservesFiniteLimits
      (closedSupportProperty X (S : Set X) (closed_finset X S hS))
    let := preservesBiproduct_of_preservesProduct F (f := family)
    let := componentSumMap_isIso X S hS M.obj.obj hM
    let e : F.obj ((sumFunctor X S hS).obj A) ≅ F.obj M :=
      F.mapBiproduct family ≪≫ asIso (componentSumMap X S hS M.obj.obj)
    exact ⟨A, ⟨F.preimageIso e⟩⟩

instance sumFunctor_isEquivalence (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) : (sumFunctor X S hS).IsEquivalence := {}

/-- The original finite summation functor gives the actual coherent support equivalence. -/
def finiteSupportEquivalence (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) :
    (∀ i : S, PointSupportCategory X S hS i) ≌ FiniteSupportCategory X S hS :=
  (sumFunctor X S hS).asEquivalence

instance sumFunctor_additive (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) : (sumFunctor X S hS).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (sumFunctor X S hS)
  exact Functor.additive_of_preservesBinaryBiproducts _

instance finiteSupportEquivalence_functor_additive (X : Scheme.{u}) [IsLocallyNoetherian X]
    (S : Finset X) (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) :
    (finiteSupportEquivalence X S hS).functor.Additive :=
  sumFunctor_additive X S hS

/-- Original singleton summation is exact for the standard abelian exact structures. -/
def sumExactFunctor (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) : CategoryTheory.ExactCategory.ExactFunctor
      (CategoryTheory.ExactCategory.abelianExactStructure
        (∀ i : S, PointSupportCategory X S hS i))
      (CategoryTheory.ExactCategory.abelianExactStructure (FiniteSupportCategory X S hS)) where
  toFunctor := sumFunctor X S hS
  map_conflation _ h := h.map_of_exact _

instance sumExactFunctor_isEquivalence (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) :
    (sumExactFunctor X S hS).toFunctor.IsEquivalence := sumFunctor_isEquivalence X S hS

/-- The inverse of the proved finite support equivalence is exact. -/
def decompositionExactFunctor (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) : CategoryTheory.ExactCategory.ExactFunctor
      (CategoryTheory.ExactCategory.abelianExactStructure (FiniteSupportCategory X S hS))
      (CategoryTheory.ExactCategory.abelianExactStructure
        (∀ i : S, PointSupportCategory X S hS i)) where
  toFunctor := (finiteSupportEquivalence X S hS).inverse
  additive := (finiteSupportEquivalence X S hS).inverse_additive
  map_conflation _ h := h.map_of_exact _

instance decompositionExactFunctor_isEquivalence (X : Scheme.{u}) [IsLocallyNoetherian X]
    (S : Finset X) (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) :
    (decompositionExactFunctor X S hS).toFunctor.IsEquivalence :=
  (finiteSupportEquivalence X S hS).isEquivalence_inverse

/-- The original singleton support inclusion is exact. -/
def pointInclusionExactFunctor (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) : CategoryTheory.ExactCategory.ExactFunctor
      (CategoryTheory.ExactCategory.abelianExactStructure (PointSupportCategory X S hS i))
      (CategoryTheory.ExactCategory.abelianExactStructure (FiniteSupportCategory X S hS)) where
  toFunctor := pointInclusion X S hS i
  map_conflation _ h := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (closedSupportProperty X (S : Set X) (closed_finset X S hS)).ι
    let := ObjectProperty.inclusion_preservesFiniteLimits
      (closedSupportProperty X {i.val} (hS i.val i.property))
    let := ObjectProperty.inclusion_preservesFiniteColimits
      (closedSupportProperty X {i.val} (hS i.val i.property))
    exact h.map_of_exact (closedSupportProperty X {i.val} (hS i.val i.property)).ι

/-- An exact coordinate of the inverse of actual finite summation. -/
def evaluationExactFunctor (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) : CategoryTheory.ExactCategory.ExactFunctor
      (CategoryTheory.ExactCategory.abelianExactStructure (FiniteSupportCategory X S hS))
      (CategoryTheory.ExactCategory.abelianExactStructure (PointSupportCategory X S hS i)) :=
  (decompositionExactFunctor X S hS).comp
    (Pi.exactEvaluation (PointSupportCategory X S hS) i)

/-- Canonical singleton insertion into the product, through the original finite-family inclusion. -/
def singletonFamily (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) :
    PointSupportCategory X S hS i ⥤ (∀ j : S, PointSupportCategory X S hS j) :=
  Pi.singletonInclusion (PointSupportCategory X S hS) i ⋙
    (Pi.finiteCategoryInclusion (PointSupportCategory X S hS)).toFunctor

/-- The original singleton product insertion retains its own coordinate. -/
theorem singletonFamily_comp_evaluation (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) :
    singletonFamily X S hS i ⋙ Pi.eval (PointSupportCategory X S hS) i =
      𝟭 (PointSupportCategory X S hS i) :=
  Pi.singletonInclusion_comp_evaluation (PointSupportCategory X S hS) i

/-- Every other coordinate of the original singleton insertion is a zero object. -/
lemma singletonFamily_other_isZero (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i j : S) (hji : j ≠ i)
    (M : PointSupportCategory X S hS i) :
    IsZero (((singletonFamily X S hS i).obj M) j) :=
  Pi.singletonInclusion_obj_isZero (PointSupportCategory X S hS) i j hji M

/-- A singleton biproduct inclusion is invertible for arbitrary zero objects elsewhere. -/
lemma isIso_biproduct_ι_of_single {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {I : Type*} (A : I → C) [HasBiproduct A] (i : I)
    (h : ∀ j, j ≠ i → IsZero (A j)) : IsIso (biproduct.ι A i) := by
  refine ⟨⟨biproduct.π A i, by simp, ?_⟩⟩
  apply biproduct.hom_ext'
  intro j
  by_cases hj : j = i
  · subst j
    simp
  · exact (h j hj).eq_of_src _ _

/-- Original summation retains a singleton even with arbitrary zero objects off-coordinate. -/
lemma sumFunctor_singleton_ι_isIso (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X))
    (A : ∀ j : S, PointSupportCategory X S hS j) (i : S)
    (hA : ∀ j, j ≠ i → IsZero (A j)) :
    IsIso (biproduct.ι (fun j : S => (pointInclusion X S hS j).obj (A j)) i) :=
  isIso_biproduct_ι_of_single _ i
    (fun j hj => (pointInclusion X S hS j).map_isZero (hA j hj))

/-- Original singleton inclusion agrees naturally with singleton insertion followed by summation. -/
def singletonSumIso (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) :
    pointInclusion X S hS i ≅ singletonFamily X S hS i ⋙ sumFunctor X S hS := by
  let e := eqToIso (singletonFamily_comp_evaluation X S hS i)
  refine NatIso.ofComponents (fun M => ?_) ?_
  · let := sumFunctor_singleton_ι_isIso X S hS ((singletonFamily X S hS i).obj M) i
      (fun j hj => singletonFamily_other_isZero X S hS i j hj M)
    exact (pointInclusion X S hS i).mapIso (e.app M).symm ≪≫
      asIso (biproduct.ι (fun j : S => (pointInclusion X S hS j).obj
        (((singletonFamily X S hS i).obj M) j)) i)
  · intro M N f
    dsimp
    simpa [sumFunctor, Category.assoc] using
      congrArg (fun g => (pointInclusion X S hS i).map g ≫
        biproduct.ι (fun j : S => (pointInclusion X S hS j).obj
          (((singletonFamily X S hS i).obj N) j)) i) (e.inv.naturality f)

/-- The chosen inverse decomposition retains the original singleton family. -/
def pointInclusionDecompositionIso (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) :
    pointInclusion X S hS i ⋙ (finiteSupportEquivalence X S hS).inverse ≅
      singletonFamily X S hS i :=
  Functor.isoWhiskerRight (singletonSumIso X S hS i)
      (finiteSupportEquivalence X S hS).inverse ≪≫
    Functor.isoWhiskerLeft (singletonFamily X S hS i)
      (finiteSupportEquivalence X S hS).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- Original singleton inclusion followed by its own exact evaluation is the identity. -/
def pointInclusionEvaluationSelfIso (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i : S) :
    pointInclusion X S hS i ⋙ (evaluationExactFunctor X S hS i).toFunctor ≅
      𝟭 (PointSupportCategory X S hS i) :=
  Functor.isoWhiskerRight (pointInclusionDecompositionIso X S hS i)
      (Pi.eval (PointSupportCategory X S hS) i) ≪≫
    eqToIso (singletonFamily_comp_evaluation X S hS i)

/-- Original singleton inclusion has a zero object at every other exact evaluation. -/
def pointInclusionEvaluationOtherIso (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (i j : S) (hji : j ≠ i) :
    pointInclusion X S hS i ⋙ (evaluationExactFunctor X S hS j).toFunctor ≅
      (Functor.const (PointSupportCategory X S hS i)).obj (0 : PointSupportCategory X S hS j) :=
  Functor.isoWhiskerRight (pointInclusionDecompositionIso X S hS i)
      (Pi.eval (PointSupportCategory X S hS) j) ≪≫
    eqToIso (Pi.singletonInclusion_comp_evaluation_zero
      (PointSupportCategory X S hS) i j hji)

end AlgebraicGeometry.Scheme.Modules.Coherent.FiniteClosedSupport
