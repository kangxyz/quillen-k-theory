/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenLongExactSequence

/-!
# Semantic consumers for the original supported relative-open sequence

Every scheme universe and open immersion below is arbitrary. These consumers
exercise the actual support predicate, unchanged underlying chain maps, both
fine exact functors, the original supported inclusion and its genuine relative
kernel. They impose no global boundedness, affine, density or comparison
hypothesis, and they make no replacement of the coarse model by `Perfect U`.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.Waldhausen Quillen.Waldhausen.Fibration
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

-- Actual support is exactly relative acyclicity on the unchanged perfect object.
example (K : Perfect X) :
    Acyclic (perfectOpenWeakWaldhausen j) K ↔ ((restrict j).obj K.obj).Acyclic :=
  perfectOpenAcyclic_iff j K

example (K : Complex X) (hK : locallyPerfect X K) :
    Acyclic (perfectOpenNested j).coarse ⟨K, hK⟩ ↔ perfectSupported j K := by
  change Acyclic (perfectOpenWeakWaldhausen j) ⟨K, hK⟩ ↔ perfectSupported j K
  rw [perfectOpenAcyclic_iff]
  exact ⟨fun h ↦ ⟨hK, h⟩, fun h ↦ h.2⟩

example (K : (perfectSupported j).FullSubcategory) :
    Acyclic (perfectOpenWeakWaldhausen j) ((perfectSupportedToAcyclic j).obj K).obj :=
  ((perfectSupportedToAcyclic j).obj K).property

example (K : AcyclicCategory (perfectOpenNested j)) :
    perfectSupported j ((perfectAcyclicToSupported j).obj K).obj :=
  ((perfectAcyclicToSupported j).obj K).property

-- Flattening and its inverse leave the concrete complexes and chain maps alone.
example (K : AcyclicCategory (perfectOpenNested j)) :
    ((perfectAcyclicToSupported j).obj K).obj = K.obj.obj := rfl

example {K L : AcyclicCategory (perfectOpenNested j)} (f : K ⟶ L) :
    ((perfectAcyclicToSupported j).map f).hom = f.hom.hom := rfl

example (K : (perfectSupported j).FullSubcategory) :
    ((perfectSupportedToAcyclic j).obj K).obj.obj = K.obj := rfl

example {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L) :
    ((perfectSupportedToAcyclic j).map f).hom.hom = f.hom := rfl

example : perfectAcyclicToSupported j ⋙ perfectSupportedToAcyclic j =
    𝟭 (AcyclicCategory (perfectOpenNested j)) :=
  perfectAcyclicToSupported_comp_inverse j

example : perfectSupportedToAcyclic j ⋙ perfectAcyclicToSupported j =
    𝟭 ((perfectSupported j).FullSubcategory) :=
  perfectSupportedToAcyclic_comp_inverse j

example : perfectAcyclicToSupported j ⋙ ObjectProperty.ιOfLE
    (show perfectSupported j ≤ locallyPerfect X from fun _ h ↦ h.1) =
    acyclicInclusion (perfectOpenNested j) := perfectAcyclicToSupported_comp_inclusion j

example : perfectSupportedToAcyclic j ⋙ acyclicInclusion (perfectOpenNested j) =
    ObjectProperty.ιOfLE
      (show perfectSupported j ≤ locallyPerfect X from fun _ h ↦ h.1) :=
  perfectSupportedToAcyclic_comp_inclusion j

-- The inherited weak class is fine quasi-isomorphism, not merely relative weakness.
example {K L : AcyclicCategory (perfectOpenNested j)} (f : K ⟶ L) :
    (acyclicStructure (perfectOpenNested j)).weq f ↔ QuasiIso f.hom.hom := Iff.rfl

example {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (perfectSupportedWaldhausen j).weq f ↔ QuasiIso f.hom := Iff.rfl

example {K L : AcyclicCategory (perfectOpenNested j)} (f : K ⟶ L)
    (hf : (acyclicStructure (perfectOpenNested j)).cof f) :
    (perfectSupportedWaldhausen j).cof ((perfectAcyclicToSupported j).map f) :=
  (perfectAcyclicToSupported_exact j).cofibration f hf

example {K L : AcyclicCategory (perfectOpenNested j)} (f : K ⟶ L)
    (hf : (acyclicStructure (perfectOpenNested j)).weq f) :
    (perfectSupportedWaldhausen j).weq ((perfectAcyclicToSupported j).map f) :=
  (perfectAcyclicToSupported_exact j).weak f hf

example {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L)
    (hf : (perfectSupportedWaldhausen j).cof f) :
    (acyclicStructure (perfectOpenNested j)).cof ((perfectSupportedToAcyclic j).map f) :=
  (perfectSupportedToAcyclic_exact j).cofibration f hf

example {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L)
    (hf : (perfectSupportedWaldhausen j).weq f) :
    (acyclicStructure (perfectOpenNested j)).weq ((perfectSupportedToAcyclic j).map f) :=
  (perfectSupportedToAcyclic_exact j).weak f hf

-- Reflection checks the nontrivial quotient-support comparison in the opposite direction.
example {K L : AcyclicCategory (perfectOpenNested j)} (f : K ⟶ L) :
    (acyclicStructure (perfectOpenNested j)).cof f ↔
      (perfectSupportedWaldhausen j).cof ((perfectAcyclicToSupported j).map f) :=
  ⟨(perfectAcyclicToSupported_exact j).cofibration f,
    (perfectSupportedToAcyclic_exact j).cofibration ((perfectAcyclicToSupported j).map f)⟩

example {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (perfectSupportedWaldhausen j).cof f ↔
      (acyclicStructure (perfectOpenNested j)).cof ((perfectSupportedToAcyclic j).map f) :=
  ⟨(perfectSupportedToAcyclic_exact j).cofibration f,
    (perfectAcyclicToSupported_exact j).cofibration ((perfectSupportedToAcyclic j).map f)⟩

-- Both directions retain actual pushouts along the fine cofibrations.
example {A B D P : AcyclicCategory (perfectOpenNested j)}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {k : D ⟶ P}
    (hi : (acyclicStructure (perfectOpenNested j)).cof i) (h : IsPushout i f g k) :
    IsPushout ((perfectAcyclicToSupported j).map i) ((perfectAcyclicToSupported j).map f)
      ((perfectAcyclicToSupported j).map g) ((perfectAcyclicToSupported j).map k) :=
  (perfectAcyclicToSupported_exact j).pushout hi h

example {A B D P : (perfectSupported j).FullSubcategory}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {k : D ⟶ P}
    (hi : (perfectSupportedWaldhausen j).cof i) (h : IsPushout i f g k) :
    IsPushout ((perfectSupportedToAcyclic j).map i) ((perfectSupportedToAcyclic j).map f)
      ((perfectSupportedToAcyclic j).map g) ((perfectSupportedToAcyclic j).map k) :=
  (perfectSupportedToAcyclic_exact j).pushout hi h

-- Both underlying inclusion diagrams induce precisely the existing public K-map.
example (n : ℕ) :
    (perfectSupportedKMap j n).comp (perfectAcyclicSupportedKEquiv j n).toMonoidHom =
      KMap (acyclicInclusion_exact (perfectOpenNested j)) n :=
  perfectAcyclicSupportedKEquiv_inclusion j n

example (n : ℕ) :
    (KMap (acyclicInclusion_exact (perfectOpenNested j)) n).comp
      (perfectAcyclicSupportedKEquiv j n).symm.toMonoidHom = perfectSupportedKMap j n :=
  perfectAcyclicSupportedKEquiv_symm_inclusion j n

example (n : ℕ) (a : PerfectSupportedK j n) :
    perfectAcyclicSupportedKEquiv j n ((perfectAcyclicSupportedKEquiv j n).symm a) = a :=
  (perfectAcyclicSupportedKEquiv j n).apply_symm_apply a

example (n : ℕ) : Function.Bijective (perfectSupportedFiberKMap j n) :=
  perfectSupportedFiberKMap_bijective j n

example (n : ℕ) :
    (piMap n (HomotopyFiber.projection (changeWeakMap (perfectOpenNested j))
      (perfectOpenWeakWaldhausen j).kBasepoint)
      (HomotopyFiber.projection_basepoint _ _ (perfectWaldhausen X).kBasepoint
        (changeWeakMap_basepoint (perfectOpenNested j)))).comp
      (perfectSupportedFiberKMap j n) = perfectSupportedKMap j n :=
  perfectSupportedFiberKMap_projection j n

example (n : ℕ) :
    (perfectOpenKRestrict j n).comp (perfectOpenKMap j n) = perfectKRestrict j n :=
  perfectOpenKRestrict_comp_perfectOpenKMap j n

-- An arbitrary class from the original supported category maps to the actual relative kernel.
example (n : ℕ) (a : PerfectSupportedK j n) :
    perfectSupportedKMap j n a ∈ (perfectOpenKMap j n).ker := by
  rw [← range_perfectSupportedKMap_eq_ker_perfectOpenKMap j n]
  exact ⟨a, rfl⟩

example (n : ℕ) (a : PerfectSupportedK j n) :
    perfectOpenKMap j n (perfectSupportedKMap j n a) = 1 := by
  have h : perfectSupportedKMap j n a ∈ (perfectSupportedKMap j n).range := ⟨a, rfl⟩
  rw [range_perfectSupportedKMap_eq_ker_perfectOpenKMap j n] at h
  exact h

example : (perfectOpenKMap j 0).comp (perfectSupportedKMap j 0) = 1 := by
  ext a
  have h : perfectSupportedKMap j 0 a ∈ (perfectSupportedKMap j 0).range := ⟨a, rfl⟩
  rw [range_perfectSupportedKMap_eq_ker_perfectOpenKMap j 0] at h
  exact h

-- Exactness supplies a preimage in the original supported K-group, not a renamed substitute.
example (n : ℕ) (a : PerfectK X n) (ha : perfectOpenKMap j n a = 1) :
    ∃ b : PerfectSupportedK j n, perfectSupportedKMap j n b = a := by
  have h : a ∈ (perfectOpenKMap j n).ker := ha
  rw [← range_perfectSupportedKMap_eq_ker_perfectOpenKMap j n] at h
  exact h

example (n : ℕ) (a : PerfectOpenK j (n + 1)) :
    perfectSupportedKMap j n (perfectOpenConnectingHom j n a) = 1 := by
  have h : perfectOpenConnectingHom j n a ∈ (perfectOpenConnectingHom j n).range := ⟨a, rfl⟩
  rw [range_perfectOpenConnectingHom_eq_ker_perfectSupportedKMap j n] at h
  exact h

example (a : PerfectOpenK j 0) : ∃ b : PerfectK X 0, perfectOpenKMap j 0 b = a :=
  perfectOpenKMap_zero_surjective j a
