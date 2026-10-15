/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.PairPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedOpenNaturality
public import Quillen.Waldhausen.GrothendieckComparison.SmallModel

/-!
# Actual supported Grothendieck pullbacks

Fine and relative supported algebraic classes are transported through their
original K-zero comparisons and the existing supported pair pullbacks. The
bounded-flat formulas retain actual geometric pullback representatives. The
relative restriction square follows from the same actual bounded-flat square.
No exact raw-perfect pullback, density, or extension premise is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.AlgebraicGrothendieck
universe u
namespace Quillen.PerfectComplexes

/-- The original algebraic presentation computes the actual fine supported K-zero group. -/
def perfectSupportedGrothendieckKZeroEquiv {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    Multiplicative (Group (perfectSupportedWaldhausen j)) ≃* PerfectSupportedK j 0 :=
  grothendieckKZeroEquivOfSmallModel (perfectSupportedWaldhausen j)

/-- The supported object generator is its original topological object class. -/
@[simp] theorem perfectSupportedGrothendieckKZeroEquiv_objectClass {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : (perfectSupported j).FullSubcategory) :
    perfectSupportedGrothendieckKZeroEquiv j
      (Multiplicative.ofAdd (objectClass (perfectSupportedWaldhausen j) K)) =
        (perfectSupportedWaldhausen j).kZeroObjectClass K :=
  grothendieckKZeroEquivOfSmallModel_objectClass (perfectSupportedWaldhausen j) K

/-- Actual supported derived pullback on the original algebraic groups. -/
def perfectSupportedGrothendieckPullback
    {A B : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}} (f : A ⟶ B) :
    Group (perfectSupportedWaldhausen B.obj.obj.hom) →+
      Group (perfectSupportedWaldhausen A.obj.obj.hom) :=
  ((perfectSupportedGrothendieckKZeroEquiv A.obj.obj.hom).symm.toMonoidHom.comp
    ((perfectSupportedKPullback f 0).comp
      (perfectSupportedGrothendieckKZeroEquiv B.obj.obj.hom).toMonoidHom)).toAdditive

/-- The actual supported K-zero map is retained on every original algebraic class. -/
theorem perfectSupportedGrothendieckPullback_comparison
    {A B : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}} (f : A ⟶ B)
    (x : Group (perfectSupportedWaldhausen B.obj.obj.hom)) :
    perfectSupportedGrothendieckKZeroEquiv A.obj.obj.hom
        (Multiplicative.ofAdd (perfectSupportedGrothendieckPullback f x)) =
      perfectSupportedKPullback f 0
        (perfectSupportedGrothendieckKZeroEquiv B.obj.obj.hom (Multiplicative.ofAdd x)) :=
  (perfectSupportedGrothendieckKZeroEquiv A.obj.obj.hom).apply_symm_apply _

/-- Supported composition has the original contravariant order. -/
theorem perfectSupportedGrothendieckPullback_comp
    {A B C : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    perfectSupportedGrothendieckPullback (f ≫ g) =
      (perfectSupportedGrothendieckPullback f).comp (perfectSupportedGrothendieckPullback g) := by
  apply AddMonoidHom.ext
  intro x
  apply (perfectSupportedGrothendieckKZeroEquiv A.obj.obj.hom).injective
  change perfectSupportedGrothendieckKZeroEquiv A.obj.obj.hom
      (Multiplicative.ofAdd (perfectSupportedGrothendieckPullback (f ≫ g) x)) =
    perfectSupportedGrothendieckKZeroEquiv A.obj.obj.hom
      (Multiplicative.ofAdd
        (perfectSupportedGrothendieckPullback f (perfectSupportedGrothendieckPullback g x)))
  rw [perfectSupportedGrothendieckPullback_comparison,
    perfectSupportedGrothendieckPullback_comparison,
    perfectSupportedGrothendieckPullback_comparison, perfectSupportedKPullback_comp]
  rfl

/-- Supported bounded-flat representatives retain their actual geometric pair pullback. -/
theorem perfectSupportedGrothendieckPullback_boundedFlat_objectClass
    {A B : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}} (f : A ⟶ B)
    (K : (boundedFlatPerfectSupported B.obj.obj.hom).FullSubcategory) :
    perfectSupportedGrothendieckPullback f
        (objectClass (perfectSupportedWaldhausen B.obj.obj.hom)
          ((boundedFlatPerfectSupportedInclusion B.obj.obj.hom).obj K)) =
      objectClass (perfectSupportedWaldhausen A.obj.obj.hom)
        ((boundedFlatPerfectSupportedInclusion A.obj.obj.hom).obj
          ((boundedFlatPerfectSupportedPullback f.hom).obj K)) := by
  apply (perfectSupportedGrothendieckKZeroEquiv A.obj.obj.hom).injective
  change perfectSupportedGrothendieckKZeroEquiv A.obj.obj.hom
      (Multiplicative.ofAdd (perfectSupportedGrothendieckPullback f
        (objectClass (perfectSupportedWaldhausen B.obj.obj.hom)
          ((boundedFlatPerfectSupportedInclusion B.obj.obj.hom).obj K)))) =
    perfectSupportedGrothendieckKZeroEquiv A.obj.obj.hom
      (Multiplicative.ofAdd (objectClass (perfectSupportedWaldhausen A.obj.obj.hom)
        ((boundedFlatPerfectSupportedInclusion A.obj.obj.hom).obj
          ((boundedFlatPerfectSupportedPullback f.hom).obj K))))
  rw [perfectSupportedGrothendieckPullback_comparison,
    perfectSupportedGrothendieckKZeroEquiv_objectClass,
    perfectSupportedGrothendieckKZeroEquiv_objectClass]
  have h := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat f 0)
    ((boundedFlatPerfectSupportedWaldhausen B.obj.obj.hom).kZeroObjectClass K)
  change perfectSupportedKPullback f 0
      (KMap (boundedFlatPerfectSupportedInclusion_exact B.obj.obj.hom) 0
        ((boundedFlatPerfectSupportedWaldhausen B.obj.obj.hom).kZeroObjectClass K)) =
    KMap (boundedFlatPerfectSupportedInclusion_exact A.obj.obj.hom) 0
      (KMap (boundedFlatPerfectSupportedPullback_exact f.hom) 0
        ((boundedFlatPerfectSupportedWaldhausen B.obj.obj.hom).kZeroObjectClass K)) at h
  rw [KMap_kZeroObjectClass, KMap_kZeroObjectClass, KMap_kZeroObjectClass] at h
  exact h

/-- The actual relative algebraic presentation computes supported relative K-zero. -/
def perfectSupportedOpenGrothendieckKZeroEquiv {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) :
    Multiplicative (Group (perfectSupportedOpenWeakWaldhausen j T)) ≃*
      PerfectSupportedOpenK j T 0 :=
  grothendieckKZeroEquivOfSmallModel (perfectSupportedOpenWeakWaldhausen j T)

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.hom.right = g ≫ j) [CompactSpace X'] [CompactSpace X]

/-- Supported relative algebraic pullback retains the actual original K-zero pair map. -/
def perfectSupportedOpenGrothendieckPullback :
    Group (perfectSupportedOpenWeakWaldhausen j T) →+
      Group (perfectSupportedOpenWeakWaldhausen j' S) :=
  ((perfectSupportedOpenGrothendieckKZeroEquiv j' S).symm.toMonoidHom.comp
    ((perfectSupportedOpenKPullback j' j f g w 0).comp
      (perfectSupportedOpenGrothendieckKZeroEquiv j T).toMonoidHom)).toAdditive

/-- Every original relative algebraic class retains its genuine K-zero pullback value. -/
theorem perfectSupportedOpenGrothendieckPullback_comparison
    (x : Group (perfectSupportedOpenWeakWaldhausen j T)) :
    perfectSupportedOpenGrothendieckKZeroEquiv j' S
        (Multiplicative.ofAdd (perfectSupportedOpenGrothendieckPullback j' j f g w x)) =
      perfectSupportedOpenKPullback j' j f g w 0
        (perfectSupportedOpenGrothendieckKZeroEquiv j T (Multiplicative.ofAdd x)) :=
  (perfectSupportedOpenGrothendieckKZeroEquiv j' S).apply_symm_apply _

private theorem supportedOpenKRestriction_pullback [CompactSpace U'] [CompactSpace U]
    (n : ℕ) :
    (perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w))
      n).comp (perfectSupportedOpenKRestrict j T n) =
    (perfectSupportedOpenKRestrict j' S n).comp (perfectSupportedOpenKPullback j' j f g w n) := by
  ext x
  obtain ⟨y, rfl⟩ :=
    (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap_bijective j T n).surjective x
  have h₁ := DFunLike.congr_fun (boundedFlatPerfectSupportedOpenKRestrict_comparison j T n) y
  have h₂ := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat
    (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)) n)
      (boundedFlatPerfectSupportedOpenKRestrict j T n y)
  change perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)) n
      (boundedFlatPerfectSupportedToPerfectSupportedKMap (j ⁻¹ᵁ T).ι n
        (boundedFlatPerfectSupportedOpenKRestrict j T n y)) =
    boundedFlatPerfectSupportedToPerfectSupportedKMap (j' ⁻¹ᵁ S).ι n
      (boundedFlatPerfectSupportedKPullback (supportedPairTargetSquare j' j f g w) n
        (boundedFlatPerfectSupportedOpenKRestrict j T n y)) at h₂
  have h₃ := DFunLike.congr_fun (perfectSupportedOpenKPullback_comp_boundedFlat j' j f g w n) y
  have h₄ := DFunLike.congr_fun (boundedFlatPerfectSupportedOpenKRestrict_comparison j' S n)
    (boundedFlatPerfectSupportedOpenKPullback j' j f g w n y)
  have h₅ := DFunLike.congr_fun (boundedFlatPerfectSupportedOpenKRestrict_pullback j T j' f g w n) y
  exact (congrArg
    (perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)) n)
      h₁).trans
      (h₂.trans ((congrArg (boundedFlatPerfectSupportedToPerfectSupportedKMap (j' ⁻¹ᵁ S).ι n)
        h₅).trans
        (h₄.symm.trans (congrArg (perfectSupportedOpenKRestrict j' S n) h₃.symm))))

/-- The original relative restriction image square holds on actual algebraic supported classes. -/
theorem perfectSupportedOpenGrothendieckPullback_restrictionSquare
    [CompactSpace U'] [CompactSpace U] :
    (perfectSupportedGrothendieckPullback
      (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w))).comp
        (map (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
          (perfectSupportedOpenRestrict_waldhausenExact j T)) =
      (map (perfectSupportedOpenWeakWaldhausen j' S) (perfectSupportedRestrict j' S)
        (perfectSupportedOpenRestrict_waldhausenExact j' S)).comp
          (perfectSupportedOpenGrothendieckPullback j' j f g w) := by
  apply AddMonoidHom.ext
  intro x
  apply (perfectSupportedGrothendieckKZeroEquiv (j' ⁻¹ᵁ S).ι).injective
  change perfectSupportedGrothendieckKZeroEquiv (j' ⁻¹ᵁ S).ι
      (Multiplicative.ofAdd (perfectSupportedGrothendieckPullback
        (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w))
          (map (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
            (perfectSupportedOpenRestrict_waldhausenExact j T) x))) =
    perfectSupportedGrothendieckKZeroEquiv (j' ⁻¹ᵁ S).ι
      (Multiplicative.ofAdd (map (perfectSupportedOpenWeakWaldhausen j' S)
        (perfectSupportedRestrict j' S) (perfectSupportedOpenRestrict_waldhausenExact j' S)
          (perfectSupportedOpenGrothendieckPullback j' j f g w x)))
  have h₁ := grothendieckKZeroEquivOfSmallModel_natural
    (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
    (perfectSupportedRestrict j T) (perfectSupportedOpenRestrict_waldhausenExact j T)
    (Multiplicative.ofAdd x)
  have h₂ := grothendieckKZeroEquivOfSmallModel_natural
    (perfectSupportedOpenWeakWaldhausen j' S) (perfectSupportedWaldhausen (j' ⁻¹ᵁ S).ι)
    (perfectSupportedRestrict j' S) (perfectSupportedOpenRestrict_waldhausenExact j' S)
    (Multiplicative.ofAdd (perfectSupportedOpenGrothendieckPullback j' j f g w x))
  change perfectSupportedOpenKRestrict j T 0
      (perfectSupportedOpenGrothendieckKZeroEquiv j T (Multiplicative.ofAdd x)) =
    perfectSupportedGrothendieckKZeroEquiv (j ⁻¹ᵁ T).ι
      (Multiplicative.ofAdd (map (perfectSupportedOpenWeakWaldhausen j T)
        (perfectSupportedRestrict j T) (perfectSupportedOpenRestrict_waldhausenExact j T) x)) at h₁
  change perfectSupportedOpenKRestrict j' S 0
      (perfectSupportedOpenGrothendieckKZeroEquiv j' S
        (Multiplicative.ofAdd (perfectSupportedOpenGrothendieckPullback j' j f g w x))) =
    perfectSupportedGrothendieckKZeroEquiv (j' ⁻¹ᵁ S).ι
      (Multiplicative.ofAdd (map (perfectSupportedOpenWeakWaldhausen j' S)
        (perfectSupportedRestrict j' S) (perfectSupportedOpenRestrict_waldhausenExact j' S)
          (perfectSupportedOpenGrothendieckPullback j' j f g w x))) at h₂
  have h₀ := perfectSupportedGrothendieckPullback_comparison
    (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w))
    (map (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
      (perfectSupportedOpenRestrict_waldhausenExact j T) x)
  have h₃ := DFunLike.congr_fun (supportedOpenKRestriction_pullback j' j f g w 0)
    (perfectSupportedOpenGrothendieckKZeroEquiv j T (Multiplicative.ofAdd x))
  exact h₀.trans
    ((congrArg (perfectSupportedKPullback
      (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)) 0) h₁.symm).trans
      (h₃.trans
        ((congrArg (perfectSupportedOpenKRestrict j' S 0)
          (perfectSupportedOpenGrothendieckPullback_comparison j' j f g w x).symm).trans h₂)))


end Quillen.PerfectComplexes
