/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Fibration

/-!
# Actual bounded-flat models for supported relative K-theory

The original bounded-flat supported category is given weak equivalences
detected by actual open restriction. Fine supported approximation and the
genuine original cone cylinder prove that its literal inclusion into the
existing supported relative category induces a K-equivalence in every
connective degree, including K0. The original change-of-weak square commutes.
Only compactness of the ambient scheme X is required for the comparison;
neither the localization open U nor the auxiliary acyclicity open T is
assumed compact, and no separation hypothesis is imposed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The actual bounded-flat category with weak maps detected on the open. -/
def boundedFlatPerfectSupportedOpenWaldhausen : Waldhausen.Structure ((boundedFlatPerfectSupported
  T.ι).FullSubcategory) :=
  Waldhausen.Structure.withInverseImageWeak
    ((boundedFlatPerfectSupportedInclusion_exact T.ι).comp (perfectSupportedRestrict_exact j T))

/-- The original quasi-isomorphisms included in the weak maps detected on the open. -/
def boundedFlatPerfectSupportedOpenNested :
    Waldhausen.Fibration.NestedWeakEquivalences (boundedFlatPerfectSupportedWaldhausen T.ι) :=
  Waldhausen.Structure.inverseImageWeakNested
    ((boundedFlatPerfectSupportedInclusion_exact T.ι).comp (perfectSupportedRestrict_exact j T))

/-- The unchanged inclusion is exact for the actual relative weak structures. -/
theorem boundedFlatPerfectSupportedOpenInclusion_exact :
    Waldhausen.IsExact (boundedFlatPerfectSupportedOpenWaldhausen j T).cof
      (boundedFlatPerfectSupportedOpenWaldhausen j T).weq (perfectSupportedOpenWeakWaldhausen j
        T).cof
      (perfectSupportedOpenWeakWaldhausen j T).weq (boundedFlatPerfectSupportedInclusion T.ι) where
  zero := (boundedFlatPerfectSupportedInclusion_exact T.ι).zero
  cofibration := (boundedFlatPerfectSupportedInclusion_exact T.ι).cofibration
  weak _ h := h
  pushout := (boundedFlatPerfectSupportedInclusion_exact T.ι).pushout

/-- The relative-open source uses the genuine original bounded-flat cylinder. -/
def boundedFlatPerfectSupportedOpenJointData :
    Waldhausen.Fibration.RowFactorization.JointData (boundedFlatPerfectSupportedOpenNested j T) :=
  Waldhausen.Fibration.complexJointDataOfNested (boundedFlatPerfectSupported T.ι)
    (fun hK hL f => boundedFlatPerfectSupported_mappingCone T.ι hK hL f)
    (fun _ hK => boundedFlatPerfectSupported_shift T.ι hK 1) (boundedFlatPerfectSupportedOpenNested
      j T)

/-- Fine relative replacements already prove App2 onto the same original
relative-open objects; this does not assert extension from the open. -/
theorem boundedFlatPerfectSupportedOpenInclusion_approximation [CompactSpace X] :
    Waldhausen.HasApproximationProperty (boundedFlatPerfectSupportedOpenWaldhausen j T)
      (perfectSupportedOpenWeakWaldhausen j T) (boundedFlatPerfectSupportedInclusion T.ι) where
  reflects _ h := h
  lift f := by
    obtain ⟨M, i, p, hi, hp, hfac⟩ := (boundedFlatPerfectSupportedInclusion_approximation T.ι).lift
      f
    exact ⟨M, i, p, hi, (perfectSupportedOpenNested j T).le_weq p hp, hfac⟩

/-- The connective K-groups of the bounded-flat supported relative-open category. -/
abbrev BoundedFlatPerfectSupportedOpenK (n : ℕ) := (boundedFlatPerfectSupportedOpenWaldhausen j T).K
  n

/-- The original K-map that enlarges weak equivalences by testing on the open. -/
def boundedFlatPerfectSupportedOpenKMap (n : ℕ) :
    BoundedFlatPerfectSupportedK T.ι n →* BoundedFlatPerfectSupportedOpenK j T n :=
  Waldhausen.KMap (Waldhausen.Fibration.changeWeak_exact (boundedFlatPerfectSupportedOpenNested j
    T)) n

/-- The K-map of the actual inclusion into supported relative perfect complexes. -/
def boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap (n : ℕ) :
    BoundedFlatPerfectSupportedOpenK j T n →* PerfectSupportedOpenK j T n :=
  Waldhausen.KMap (boundedFlatPerfectSupportedOpenInclusion_exact j T) n

/-- The ORIGINAL relative-open target is unchanged, in every connective degree. -/
theorem boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap_bijective [CompactSpace X] (n : ℕ)
  :
    Function.Bijective (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j T n) :=
  Waldhausen.Fibration.coarse_KMap_bijective (boundedFlatPerfectSupportedOpenNested j T)
    (boundedFlatPerfectSupportedOpenJointData j T)
      (boundedFlatPerfectSupportedOpenInclusion_approximation j T)
    (boundedFlatPerfectSupportedOpenInclusion_exact j T) n

/-- For a compact ambient scheme, the equivalence induced by the original bounded-flat inclusion. -/
def boundedFlatPerfectSupportedOpenKEquiv [CompactSpace X] (n : ℕ) :
    BoundedFlatPerfectSupportedOpenK j T n ≃* PerfectSupportedOpenK j T n :=
  MulEquiv.ofBijective (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j T n)
    (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap_bijective j T n)

@[simp] theorem boundedFlatPerfectSupportedOpenKEquiv_toMonoidHom [CompactSpace X] (n : ℕ) :
    (boundedFlatPerfectSupportedOpenKEquiv j T n :
      BoundedFlatPerfectSupportedOpenK j T n →* PerfectSupportedOpenK j T n) =
      boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j T n := rfl

/-- The unchanged original change-of-weak-equivalences map commutes with the
literal bounded-flat inclusion comparisons. -/
theorem boundedFlatPerfectSupportedOpenToPerfectSupportedOpen_comp (n : ℕ) :
    (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j T n).comp
      (boundedFlatPerfectSupportedOpenKMap j T n) =
      (perfectSupportedOpenKMap j T n).comp (boundedFlatPerfectSupportedToPerfectSupportedKMap T.ι
        n) := by
  unfold boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap
    boundedFlatPerfectSupportedOpenKMap
    perfectSupportedOpenKMap boundedFlatPerfectSupportedToPerfectSupportedKMap
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]

end Quillen.PerfectComplexes

end
