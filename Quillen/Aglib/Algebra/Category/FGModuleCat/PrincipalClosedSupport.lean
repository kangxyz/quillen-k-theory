/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Aglib.Algebra.Category.FGModuleCat.Localization
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# Finite modules on a principal closed subscheme

Restriction of scalars along R → R/(f) is an actual exact fully faithful functor.
Its essential image consists precisely of finite R-modules killed by f. This
subcategory is smaller than the f-power-torsion support category; the comparison
between their G-theories requires dévissage, not a categorical equivalence.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open ModuleCat.FiniteLocalization


open ModuleCat

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.FiniteModuleLocalization
variable {R : Type u} [CommRing R] (f : R)

/-- The coordinate ring of the principal closed subscheme V(f). -/
abbrev ClosedRing := R ⧸ Ideal.span {f}

/-- Finite modules killed by f, rather than merely killed by a power of f. -/
def killedBy : ObjectProperty (FGModuleCat.{u} R) := fun M ↦ ∀ m : M, f • m = 0

/-- Actual restriction of scalars along the quotient ring map. -/
def closedRestriction : FGModuleCat.{u} (ClosedRing f) ⥤ FGModuleCat.{u} R :=
  ObjectProperty.lift _
    (forget₂ (FGModuleCat (ClosedRing f)) (ModuleCat (ClosedRing f)) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))) (fun M ↦ by
    change Module.Finite R ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
      M.obj)
    let N := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj M.obj
    have : Module.Finite (ClosedRing f) N := M.property
    have : IsScalarTower R (ClosedRing f) N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact Module.Finite.trans (ClosedRing f) N)

@[simp] theorem closedRestriction_obj_obj (M : FGModuleCat.{u} (ClosedRing f)) :
    ((closedRestriction f).obj M).obj =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj M.obj := rfl

@[simp] theorem closedRestriction_map_hom {M N : FGModuleCat.{u} (ClosedRing f)} (g : M ⟶ N) :
    ((closedRestriction f).map g).hom =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).map g.hom := rfl

/-- Every quotient-ring module is annihilated by the defining element. -/
theorem closedRestriction_killed (M : FGModuleCat.{u} (ClosedRing f)) :
    killedBy f ((closedRestriction f).obj M) := by
  intro m
  change M at m
  change (Ideal.Quotient.mk (Ideal.span {f}) f) • (m : M) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f)), zero_smul]

/-- Restriction of scalars, with codomain restricted to the actual annihilated objects. -/
def closedToKilled : FGModuleCat.{u} (ClosedRing f) ⥤ (killedBy f).FullSubcategory :=
  ObjectProperty.lift _ (closedRestriction f) (closedRestriction_killed f)

/-- Surjectivity of R → R/(f) makes quotient-ring linearity recoverable from R-linearity. -/
def fullyFaithfulClosedRestriction : (closedRestriction f).FullyFaithful where
  preimage {M N} g := FGModuleCat.ofHom
    { toFun := g.hom.hom
      map_add' := g.hom.hom.map_add
      map_smul' := by
        intro a m
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact g.hom.hom.map_smul r m }

instance closedRestriction_full : (closedRestriction f).Full := (fullyFaithfulClosedRestriction
  f).full
instance closedRestriction_faithful : (closedRestriction f).Faithful :=
  (fullyFaithfulClosedRestriction f).faithful

instance closedToKilled_full : (closedToKilled f).Full := by
  constructor
  intro M N g
  obtain ⟨h, hh⟩ := (closedRestriction f).map_surjective g.hom
  exact ⟨h, ObjectProperty.hom_ext _ hh⟩

instance closedToKilled_faithful : (closedToKilled f).Faithful where
  map_injective h := (closedRestriction f).map_injective (congrArg (fun k ↦ k.hom) h)

/-- Every finite annihilated R-module has its genuine quotient-ring module structure. -/
instance closedToKilled_essSurj : (closedToKilled f).EssSurj where
  mem_essImage M := by
    have hM : Module.IsTorsionBy R M.obj f := M.property
    let : Module (ClosedRing f) M.obj := hM.module
    let : IsScalarTower R (ClosedRing f) M.obj :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let : Module.Finite (ClosedRing f) M.obj :=
      Module.Finite.of_restrictScalars_finite R (ClosedRing f) M.obj
    refine ⟨FGModuleCat.of (ClosedRing f) M.obj, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact (LinearEquiv.refl R M.obj).toModuleIso

instance closedToKilled_isEquivalence : (closedToKilled f).IsEquivalence := {}

/-- The actual quotient-ring restriction equivalence onto exactly the f-killed objects. -/
def closedEquivalence : FGModuleCat.{u} (ClosedRing f) ≌ (killedBy f).FullSubcategory :=
  (closedToKilled f).asEquivalence

/-- This equivalence followed by the full inclusion is the actual restriction of scalars. -/
theorem closedEquivalence_comp_inclusion :
    (closedEquivalence f).functor ⋙ (killedBy f).ι = closedRestriction f := rfl

instance closedRestriction_additive : (closedRestriction f).Additive where
  map_add := by intros; apply FGModuleCat.hom_ext; rfl

instance closedToKilled_additive : (closedToKilled f).Additive where
  map_add := by intros; apply ObjectProperty.hom_ext; apply FGModuleCat.hom_ext; rfl

variable [IsNoetherianRing R]

instance closedRestriction_preservesFiniteLimits : PreservesFiniteLimits (closedRestriction f) := by
  have : PreservesFiniteLimits
      (closedRestriction f ⋙ forget₂ (FGModuleCat R) (ModuleCat R)) := by
    change PreservesFiniteLimits
      (forget₂ (FGModuleCat (ClosedRing f)) (ModuleCat (ClosedRing f)) ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f})))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (closedRestriction f)
    (forget₂ (FGModuleCat R) (ModuleCat R))

instance closedRestriction_preservesFiniteColimits : PreservesFiniteColimits (closedRestriction f)
  := by
  have : PreservesFiniteColimits
      (closedRestriction f ⋙ forget₂ (FGModuleCat R) (ModuleCat R)) := by
    change PreservesFiniteColimits
      (forget₂ (FGModuleCat (ClosedRing f)) (ModuleCat (ClosedRing f)) ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f})))
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (closedRestriction f)
    (forget₂ (FGModuleCat R) (ModuleCat R))

/-- The genuine principal closed pushforward on finite modules is exact. -/
def closedRestrictionExact :
    ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing f))
      (ModuleCat.finiteModuleExactStructure.{u, u} R) where
  toFunctor := closedRestriction f
  map_conflation _ h := h.map_of_exact _

instance killed_hasFiniteProducts : HasFiniteProducts (killedBy f).FullSubcategory where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (closedEquivalence f).inverse

/-- The annihilated subcategory is abelian, although it is not generally Serre
inside all finite R-modules: extensions may only be annihilated by f². -/
instance instAbelianKilledBy : Abelian (killedBy f).FullSubcategory :=
  abelianOfEquivalence (closedEquivalence f).inverse

/-- The actual quotient equivalence is an exact functor for standard abelian structures. -/
def closedToKilledExact :
    ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing f))
      (abelianExactStructure (killedBy f).FullSubcategory) where
  toFunctor := closedToKilled f
  map_conflation _ h := h.map_of_exact _

/-- The killed subcategory inclusion is the actual restriction of scalars,
composed with the inverse of the proved quotient equivalence. -/
def killedInclusionComparison :
    (closedEquivalence f).inverse ⋙ closedRestriction f ≅ (killedBy f).ι := by
  change (closedEquivalence f).inverse ⋙ ((closedEquivalence f).functor ⋙ (killedBy f).ι) ≅ _
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (closedEquivalence f).counitIso _ ≪≫ Functor.leftUnitor _

instance killedInclusion_preservesFiniteLimits : PreservesFiniteLimits (killedBy f).ι :=
  preservesFiniteLimits_of_natIso (killedInclusionComparison f)

instance killedInclusion_preservesFiniteColimits : PreservesFiniteColimits (killedBy f).ι :=
  preservesFiniteColimits_of_natIso (killedInclusionComparison f)

/-- The inclusion of the killed subcategory into finite R-modules is genuinely exact. -/
def killedInclusionExact : ExactFunctor (abelianExactStructure (killedBy f).FullSubcategory)
    (ModuleCat.finiteModuleExactStructure.{u, u} R) where
  toFunctor := (killedBy f).ι
  map_conflation _ h := h.map_of_exact _

omit [IsNoetherianRing R] in
/-- Killed modules lie in the genuine principal-open support category. -/
theorem killedBy_le_torsion : killedBy f ≤ torsion (Submonoid.powers f) := by
  intro M hM
  apply (torsion_powers_iff_uniform f M).2
  exact ⟨1, by simpa only [killedBy, pow_one] using hM⟩

/-- Closed restriction lands in the actual supported finite-module category. -/
def closedToSupport : FGModuleCat.{u} (ClosedRing f) ⥤
    (torsion (Submonoid.powers f)).FullSubcategory :=
  ObjectProperty.lift _ (closedRestriction f) fun M ↦
    killedBy_le_torsion f ((closedRestriction f).obj M) (closedRestriction_killed f M)

omit [IsNoetherianRing R] in
/-- The supported factorization retains the actual restriction-of-scalars functor. -/
theorem closedToSupport_comp_inclusion :
    closedToSupport f ⋙ (torsion (Submonoid.powers f)).ι = closedRestriction f := rfl

end Quillen.FiniteModuleLocalization
