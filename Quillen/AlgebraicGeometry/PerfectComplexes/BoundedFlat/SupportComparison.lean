/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OpenComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenSupport

/-!
# Bounded-flat models for original supported perfect K-groups

Support remains actual acyclicity after open restriction. The genuine shifts,
cones and relative replacements retain it. The literal inclusion into original
supported perfect complexes satisfies approximation on qc ambient schemes and
induces the original K-equivalence, including K0. The actual support-forgetting
maps commute with the bounded-flat comparison square.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The property of bounded-above, stalkwise-flat locally perfect complexes on `X` whose
restriction along `j` is acyclic. -/
def boundedFlatPerfectSupported : ObjectProperty (Complex X) := fun K =>
  boundedFlatPerfect X K ∧ ((restrict j).obj K).Acyclic

instance boundedFlatPerfectSupported_containsZero : (boundedFlatPerfectSupported j).ContainsZero
  where
  exists_zero := ⟨0, isZero_zero _, boundedFlatPerfect_of_isZero (isZero_zero _),
    HomologicalComplex.acyclic_of_isZero _ ((restrict j).map_isZero (isZero_zero _))⟩

instance boundedFlatPerfectSupported_closedUnderIsomorphisms :
    (boundedFlatPerfectSupported j).IsClosedUnderIsomorphisms where
  of_iso e hK := ⟨boundedFlatPerfect_of_iso e hK.1,
    fun n => (hK.2 n).of_iso ((restrict j).mapIso e)⟩

instance boundedFlatPerfectSupported_extensionClosed :
    (abelianExactStructure (Complex X)).IsExtensionClosed (boundedFlatPerfectSupported j) where
  prop_middle {_S} hS h₁ h₃ :=
    ⟨boundedFlatPerfect_of_shortExact hS h₁.1 h₃.1,
      (hS.map_of_exact (restrict j)).acyclic_X₂ h₁.2 h₃.2⟩

instance boundedFlatPerfectSupported_closedUnderFiniteProducts :
    (boundedFlatPerfectSupported j).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (Complex X)).extensionClosed_finiteProducts (boundedFlatPerfectSupported j)

theorem boundedFlatPerfectSupported_shift {K : Complex X}
    (hK : boundedFlatPerfectSupported j K) (n : ℤ) :
    boundedFlatPerfectSupported j ((shiftFunctor (Complex X) n).obj K) := by
  refine ⟨boundedFlatPerfect_shift hK.1 n, ?_⟩
  intro i
  have hi : (((restrict j).obj K)⟦n⟧).ExactAt i := by
    rw [exactAt_iff_isZero_homology]
    exact ((exactAt_iff_isZero_homology _ _).mp (hK.2 (n+i))).of_iso
      ((CochainComplex.ShiftSequence.shiftIso U.Modules n i (n+i) rfl).app
        ((restrict j).obj K))
  exact hi.of_iso (((restrict j).commShiftIso n).app K).symm

theorem boundedFlatPerfectSupported_mappingCone {K L : Complex X}
    (hK : boundedFlatPerfectSupported j K) (hL : boundedFlatPerfectSupported j L) (f : K ⟶ L) :
    boundedFlatPerfectSupported j (CochainComplex.mappingCone f) := by
  refine ⟨boundedFlatPerfect_mappingCone hK.1 hL.1 f, ?_⟩
  have : QuasiIso ((restrict j).map f) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_exactAt _ n (hK.2 n)).mpr (hL.2 n)
  have hc := CochainComplex.mappingCone_acyclic_of_quasiIso ((restrict j).map f)
  intro n
  exact (hc n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (Scheme.Modules.restrictFunctor j)).symm

/-- The inherited complex Waldhausen structure on bounded-flat perfect complexes that become
acyclic on the open specified by `j`. -/
def boundedFlatPerfectSupportedWaldhausen :=
  Waldhausen.complexSubcategory (boundedFlatPerfectSupported j)

/-- The full-subcategory inclusion from supported bounded-flat perfect complexes into supported
locally perfect complexes. -/
def boundedFlatPerfectSupportedInclusion :
    (boundedFlatPerfectSupported j).FullSubcategory ⥤ (perfectSupported j).FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ h => ⟨h.1.1, h.2⟩)

theorem boundedFlatPerfectSupportedInclusion_exact :
    Waldhausen.IsExact (boundedFlatPerfectSupportedWaldhausen j).cof
      (boundedFlatPerfectSupportedWaldhausen j).weq (perfectSupportedWaldhausen j).cof
      (perfectSupportedWaldhausen j).weq (boundedFlatPerfectSupportedInclusion j) :=
  Waldhausen.subcategoryInclusion_exact _ _ (fun _ h => ⟨h.1.1, h.2⟩)

/-- Joint row-factorization data for supported bounded-flat complexes, constructed from their
mapping cones and shifts. -/
def boundedFlatPerfectSupportedJointData :
    Waldhausen.Fibration.RowFactorization.JointData
      (Waldhausen.Fibration.NestedWeakEquivalences.refl (boundedFlatPerfectSupportedWaldhausen
        j)) :=
  Waldhausen.Fibration.complexJointDataOfNested (boundedFlatPerfectSupported j)
    (fun hK hL f => boundedFlatPerfectSupported_mappingCone j hK hL f)
    (fun _ hK => boundedFlatPerfectSupported_shift j hK 1) _

/-- Genuine relative replacements stay supported: the comparison is a quasi-isomorphism,
and its admissible quotient is acyclic on the open by the actual homology sequence. -/
theorem boundedFlatPerfectSupportedInclusion_approximation [CompactSpace X] :
    Waldhausen.HasApproximationProperty (boundedFlatPerfectSupportedWaldhausen j)
      (perfectSupportedWaldhausen j) (boundedFlatPerfectSupportedInclusion j) where
  reflects _ h := h
  lift {K L} f := by
    let K' : BoundedFlatPerfect X := ⟨K.obj, K.property.1⟩
    let L' : Perfect X := ⟨L.obj, L.property.1⟩
    let f' : (boundedFlatPerfectInclusion X).obj K' ⟶ L' := ObjectProperty.homMk f.hom
    obtain ⟨M, i, p, hi, hp, hfac⟩ := (boundedFlatPerfectInclusion_approximation X).lift f'
    let : QuasiIso p.hom := hp
    have : QuasiIso ((restrict j).map p.hom) := restrict_quasiIso j p.hom
    have hMa : ((restrict j).obj M.obj).Acyclic := fun n =>
      (exactAt_iff_of_quasiIsoAt ((restrict j).map p.hom) n).mpr (L.property.2 n)
    obtain ⟨Q, hQ, q, w, hS⟩ := (ExactSubcategory.inflation_iff
      (abelianExactStructure (Complex X)) (boundedFlatPerfect X) i).mp hi
    have hQa : ((restrict j).obj Q).Acyclic := by
      have hSi : QuasiIso ((restrict j).map i.hom) := by
        rw [quasiIso_iff]
        intro n
        exact (quasiIsoAt_iff_exactAt _ n (K.property.2 n)).mpr (hMa n)
      exact (hS.map_of_exact (restrict j)).acyclic_X₃ hSi
    let M' : (boundedFlatPerfectSupported j).FullSubcategory := ⟨M.obj, M.property, hMa⟩
    let i' : K ⟶ M' := ObjectProperty.homMk i.hom
    let p' : (boundedFlatPerfectSupportedInclusion j).obj M' ⟶ L := ObjectProperty.homMk p.hom
    refine ⟨M', i', p', ?_, hp, ?_⟩
    · exact (ExactSubcategory.inflation_iff (abelianExactStructure (Complex X))
        (boundedFlatPerfectSupported j) i').mpr ⟨Q, ⟨hQ, hQa⟩, q, w, hS⟩
    · apply ObjectProperty.hom_ext
      exact congrArg (fun s => s.hom) hfac

/-- The degree-`n` Waldhausen K-group of bounded-flat perfect complexes on `X` whose restriction
along `j` is acyclic. -/
abbrev BoundedFlatPerfectSupportedK (n : ℕ) := (boundedFlatPerfectSupportedWaldhausen j).K n

/-- The degree-`n` K-map induced by including supported bounded-flat perfect complexes into
supported locally perfect complexes. -/
def boundedFlatPerfectSupportedToPerfectSupportedKMap (n : ℕ) :
    BoundedFlatPerfectSupportedK j n →* PerfectSupportedK j n :=
  Waldhausen.KMap (boundedFlatPerfectSupportedInclusion_exact j) n

theorem boundedFlatPerfectSupportedToPerfectSupportedKMap_bijective [CompactSpace X] (n : ℕ) :
    Function.Bijective (boundedFlatPerfectSupportedToPerfectSupportedKMap j n) := by
  let : (perfectSupportedWaldhausen j).weq.HasTwoOutOfThreeProperty :=
    Waldhausen.complexSubcategory_saturated (perfectSupported j)
  exact (boundedFlatPerfectSupportedInclusion_approximation j).KMap_bijective_general
    (boundedFlatPerfectSupportedInclusion_exact j) (boundedFlatPerfectSupportedJointData j) n

/-- For quasi-compact `X`, the multiplicative equivalence from supported bounded-flat K-theory to
supported perfect K-theory with the inclusion as its forward map. -/
def boundedFlatPerfectSupportedKEquiv [CompactSpace X] (n : ℕ) :
    BoundedFlatPerfectSupportedK j n ≃* PerfectSupportedK j n :=
  MulEquiv.ofBijective (boundedFlatPerfectSupportedToPerfectSupportedKMap j n)
    (boundedFlatPerfectSupportedToPerfectSupportedKMap_bijective j n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem boundedFlatPerfectSupportedKEquiv_coe [CompactSpace X] (n : ℕ) :
    ↑(boundedFlatPerfectSupportedKEquiv j n) =
      boundedFlatPerfectSupportedToPerfectSupportedKMap j n := rfl

/-- The degree-`n` K-map that forgets the support condition on bounded-flat perfect complexes on
`X`. -/
def boundedFlatPerfectSupportedKMap (n : ℕ) :
    BoundedFlatPerfectSupportedK j n →* BoundedFlatPerfectK X n :=
  Waldhausen.subcategoryKMap (boundedFlatPerfectSupported j) (boundedFlatPerfect X)
    (fun _ h => h.1) n

/-- The original support-forgetting map commutes with the literal bounded-flat comparisons. -/
theorem boundedFlatPerfectSupportedToPerfectSupported_comp (n : ℕ) :
    (perfectSupportedKMap j n).comp (boundedFlatPerfectSupportedToPerfectSupportedKMap j n) =
      (boundedFlatPerfectToPerfectKMap X n).comp (boundedFlatPerfectSupportedKMap j n) := by
  unfold perfectSupportedKMap boundedFlatPerfectSupportedToPerfectSupportedKMap
    boundedFlatPerfectToPerfectKMap boundedFlatPerfectSupportedKMap Waldhausen.subcategoryKMap
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]

end Quillen.PerfectComplexes
