/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.BoundedFlat.KComparison
import Quillen.PerfectComplexes.OpenFibration
import Quillen.Waldhausen.Approximation.CoarseKEquivalence

/-!
# Bounded-flat models for the original relative-open K-groups

Only the weak class is enlarged, by actual restriction on the open. Fine
relative replacement already proves approximation onto the original relative
model on qc ambient schemes; its unchanged inclusion K-map is bijective in all
connective degrees. This does not identify that endpoint with all perfect
complexes on the open, and imposes no qc hypothesis on the open itself.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual bounded-flat category with weak maps detected on the open. -/
def boundedFlatPerfectOpenWaldhausen : Waldhausen.Structure (BoundedFlatPerfect X) :=
  Waldhausen.Structure.withInverseImageWeak
    ((boundedFlatPerfectInclusion_exact X).comp (perfectRestrict_waldhausenExact j))

def boundedFlatPerfectOpenNested :
    Waldhausen.Fibration.NestedWeakEquivalences (boundedFlatPerfectWaldhausen X) :=
  Waldhausen.Structure.inverseImageWeakNested
    ((boundedFlatPerfectInclusion_exact X).comp (perfectRestrict_waldhausenExact j))

/-- The unchanged inclusion is exact for the actual relative weak structures. -/
theorem boundedFlatPerfectOpenInclusion_exact :
    Waldhausen.IsExact (boundedFlatPerfectOpenWaldhausen j).cof
      (boundedFlatPerfectOpenWaldhausen j).weq (perfectOpenWeakWaldhausen j).cof
      (perfectOpenWeakWaldhausen j).weq (boundedFlatPerfectInclusion X) where
  zero := (boundedFlatPerfectInclusion_exact X).zero
  cofibration := (boundedFlatPerfectInclusion_exact X).cofibration
  weak _ h := h
  pushout := (boundedFlatPerfectInclusion_exact X).pushout

/-- The relative-open source uses the genuine original bounded-flat cylinder. -/
def boundedFlatPerfectOpenJointData :
    Waldhausen.Fibration.RowFactorization.JointData (boundedFlatPerfectOpenNested j) :=
  Waldhausen.Fibration.complexJointDataOfNested (boundedFlatPerfect X)
    (fun hK hL f => boundedFlatPerfect_mappingCone hK hL f)
    (fun _ hK => boundedFlatPerfect_shift hK 1) (boundedFlatPerfectOpenNested j)

/-- Fine relative replacements already prove App2 onto the same original
relative-open objects; this does not assert extension from the open. -/
theorem boundedFlatPerfectOpenInclusion_approximation [CompactSpace X] :
    Waldhausen.HasApproximationProperty (boundedFlatPerfectOpenWaldhausen j)
      (perfectOpenWeakWaldhausen j) (boundedFlatPerfectInclusion X) where
  reflects _ h := h
  lift f := by
    obtain ⟨M, i, p, hi, hp, hfac⟩ := (boundedFlatPerfectInclusion_approximation X).lift f
    exact ⟨M, i, p, hi, (perfectOpenNested j).le_weq p hp, hfac⟩

abbrev BoundedFlatPerfectOpenK (n : ℕ) := (boundedFlatPerfectOpenWaldhausen j).K n

def boundedFlatPerfectOpenKMap (n : ℕ) :
    BoundedFlatPerfectK X n →* BoundedFlatPerfectOpenK j n :=
  Waldhausen.KMap (Waldhausen.Fibration.changeWeak_exact (boundedFlatPerfectOpenNested j)) n

def boundedFlatPerfectOpenToPerfectOpenKMap (n : ℕ) :
    BoundedFlatPerfectOpenK j n →* PerfectOpenK j n :=
  Waldhausen.KMap (boundedFlatPerfectOpenInclusion_exact j) n

/-- The ORIGINAL relative-open target is unchanged, in every connective degree. -/
theorem boundedFlatPerfectOpenToPerfectOpenKMap_bijective [CompactSpace X] (n : ℕ) :
    Function.Bijective (boundedFlatPerfectOpenToPerfectOpenKMap j n) :=
  Waldhausen.Fibration.coarse_KMap_bijective (boundedFlatPerfectOpenNested j)
    (boundedFlatPerfectOpenJointData j) (boundedFlatPerfectOpenInclusion_approximation j)
    (boundedFlatPerfectOpenInclusion_exact j) n

def boundedFlatPerfectOpenKEquiv [CompactSpace X] (n : ℕ) :
    BoundedFlatPerfectOpenK j n ≃* PerfectOpenK j n :=
  MulEquiv.ofBijective (boundedFlatPerfectOpenToPerfectOpenKMap j n)
    (boundedFlatPerfectOpenToPerfectOpenKMap_bijective j n)

@[simp] theorem boundedFlatPerfectOpenKEquiv_toMonoidHom [CompactSpace X] (n : ℕ) :
    (boundedFlatPerfectOpenKEquiv j n).toMonoidHom =
      boundedFlatPerfectOpenToPerfectOpenKMap j n := rfl

/-- The unchanged original change-of-weak-equivalences map commutes with the
literal bounded-flat inclusion comparisons. -/
theorem boundedFlatPerfectOpenToPerfectOpen_comp (n : ℕ) :
    (boundedFlatPerfectOpenToPerfectOpenKMap j n).comp (boundedFlatPerfectOpenKMap j n) =
      (perfectOpenKMap j n).comp (boundedFlatPerfectToPerfectKMap X n) := by
  unfold boundedFlatPerfectOpenToPerfectOpenKMap boundedFlatPerfectOpenKMap
    perfectOpenKMap boundedFlatPerfectToPerfectKMap
  rw [← Waldhausen.KMap_comp, ← Waldhausen.KMap_comp]

end Quillen.PerfectComplexes
