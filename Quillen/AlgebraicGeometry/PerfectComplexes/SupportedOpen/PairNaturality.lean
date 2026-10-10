/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedOpenNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.GlobalLocalization

/-!
# Original supported localization naturality for arbitrary ambient pairs

All original relative maps and boundaries commute with the existing public
supported pair pullbacks. Relative boundary naturality needs only compact
ambient schemes; target restriction additionally needs compact localization
opens. For qcqs ambient schemes and compact localization and auxiliary opens,
the actual target boundary and positive inverse are natural, including K1→K0.
The union-fiber and absolute restriction squares retain the original public
maps. Neither flatness nor cartesianness is assumed, and no full-target K0
surjectivity is inferred.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.hom.right = g ≫ j)
  [CompactSpace X'] [CompactSpace X]

/-- Actual relative boundary naturality for arbitrary commuting support/localization
squares; the fiber map is the existing public supported pair pullback. -/
theorem perfectSupportedOpenConnectingHom_pullback (n : ℕ) :
    (perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) n).comp
        (perfectSupportedOpenConnectingHom j T n) =
      (perfectSupportedOpenConnectingHom j' S n).comp
        (perfectSupportedOpenKPullback j' j f g w (n+1)) := by
  ext x
  obtain ⟨y, rfl⟩ :=
    (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap_bijective j T (n+1)).surjective x
  have h₁ := DFunLike.congr_fun (boundedFlatPerfectSupportedOpenConnectingHom_comparison j T n) y
  have h₂ := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat
    (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) n)
      (boundedFlatPerfectSupportedOpenConnectingHom j T n y)
  change perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) n
      (boundedFlatPerfectSupportedToPerfectSupportedKMap (T ⊔ j.opensRange).ι n
        (boundedFlatPerfectSupportedOpenConnectingHom j T n y)) =
    boundedFlatPerfectSupportedToPerfectSupportedKMap (S ⊔ j'.opensRange).ι n
      (boundedFlatPerfectSupportedKPullback (supportedPairUnionSquare j' j f g w) n
        (boundedFlatPerfectSupportedOpenConnectingHom j T n y)) at h₂
  have h₃ := DFunLike.congr_fun (boundedFlatPerfectSupportedOpenConnectingHom_pullback j' j f g w n)
    y
  have h₄ := DFunLike.congr_fun (boundedFlatPerfectSupportedOpenConnectingHom_comparison j' S n)
    (boundedFlatPerfectSupportedOpenKPullback j' j f g w (n+1) y)
  have h₅ := DFunLike.congr_fun (perfectSupportedOpenKPullback_comp_boundedFlat j' j f g w (n+1)) y
  exact (congrArg
    (perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) n)
      h₁.symm).trans
      (h₂.trans ((congrArg (boundedFlatPerfectSupportedToPerfectSupportedKMap (S ⊔ j'.opensRange).ι
        n) h₃).trans
        (h₄.trans (congrArg (perfectSupportedOpenConnectingHom j' S n) h₅.symm))))

variable [CompactSpace U'] [CompactSpace U]

/-- Original relative restriction commutes with the existing public supported
pullback on the actual inverse-image support square over the localization opens. -/
theorem perfectSupportedOpenKRestrict_pullback (n : ℕ) :
    (perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w))
      n).comp
        (perfectSupportedOpenKRestrict j T n) =
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

end Quillen.PerfectComplexes

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes
variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.hom.right = g ≫ j)
  [CompactSpace X'] [CompactSpace X] [QuasiSeparatedSpace X'] [QuasiSeparatedSpace X]
  [CompactSpace U'] [CompactSpace U]
  (hS : IsCompact (S : Set X')) (hT : IsCompact (T : Set X))

/-- The original supported qcqs boundary is natural for arbitrary commuting
support and localization squares, including its K1-to-K0 instance. -/
theorem qcqsPerfectSupportedConnectingHom_pullback (n : ℕ) :
    (perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) n).comp
        (qcqsPerfectSupportedConnectingHom j T hT n) =
      (qcqsPerfectSupportedConnectingHom j' S hS n).comp
        (perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w))
          (n+1)) := by
  ext x
  obtain ⟨a, rfl⟩ := (qcqs_perfectSupportedOpenKRestrict_succ_bijective j T hT n).surjective x
  have h₁ := DFunLike.congr_fun (qcqsPerfectSupportedConnectingHom_comp_relative j T hT n) a
  have h₂ := DFunLike.congr_fun (perfectSupportedOpenConnectingHom_pullback j' j f g w n) a
  have h₃ := DFunLike.congr_fun (perfectSupportedOpenKRestrict_pullback j' j f g w (n+1)) a
  have h₄ := DFunLike.congr_fun (qcqsPerfectSupportedConnectingHom_comp_relative j' S hS n)
    (perfectSupportedOpenKPullback j' j f g w (n+1) a)
  exact (congrArg
    (perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) n)
      h₁).trans
      (h₂.trans (h₄.symm.trans
        (congrArg (qcqsPerfectSupportedConnectingHom j' S hS n) h₃.symm)))

/-- The original positive inverse endpoint retains the same public target pullback. -/
theorem qcqsPerfectSupportedOpenKEquiv_symm_pullback (n : ℕ)
    (x : PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1)) :
    perfectSupportedOpenKPullback j' j f g w (n+1)
        ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x) =
      (qcqsPerfectSupportedOpenKEquiv j' S hS n).symm
        (perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w))
          (n+1) x) := by
  apply (qcqsPerfectSupportedOpenKEquiv j' S hS n).injective
  have h := DFunLike.congr_fun (perfectSupportedOpenKRestrict_pullback j' j f g w (n+1))
    ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x)
  change perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w))
    (n+1)
      (qcqsPerfectSupportedOpenKEquiv j T hT n ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x)) =
    qcqsPerfectSupportedOpenKEquiv j' S hS n
      (perfectSupportedOpenKPullback j' j f g w (n+1)
        ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x)) at h
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm.trans (MulEquiv.apply_symm_apply _ _).symm

end Quillen.PerfectComplexes

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

section Comparison
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

lemma boundedFlatPerfectSupportedUnionKMap_comparison (n : ℕ) :
    (perfectSupportedUnionKMap j T n).comp
        (boundedFlatPerfectSupportedToPerfectSupportedKMap (T ⊔ j.opensRange).ι n) =
      (boundedFlatPerfectSupportedToPerfectSupportedKMap T.ι n).comp
        (boundedFlatPerfectSupportedUnionKMap j T n) := by
  unfold perfectSupportedUnionKMap boundedFlatPerfectSupportedUnionKMap
    boundedFlatPerfectSupportedToPerfectSupportedKMap Waldhausen.subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

end Comparison

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens} (f : supportOpenPair S ⟶
    supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.hom.right = g ≫ j)

lemma boundedFlatPerfectSupportedUnionKMap_pullback (n : ℕ) :
    (boundedFlatPerfectSupportedKPullback f n).comp
        (boundedFlatPerfectSupportedUnionKMap j T n) =
      (boundedFlatPerfectSupportedUnionKMap j' S n).comp
        (boundedFlatPerfectSupportedKPullback (supportedPairUnionSquare j' j f g w) n) := by
  unfold boundedFlatPerfectSupportedKPullback boundedFlatPerfectSupportedUnionKMap
    Waldhausen.subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

variable [CompactSpace X'] [CompactSpace X]

lemma perfectSupportedUnionKMap_pullback (n : ℕ) :
    (perfectSupportedKPullback (qcSupportedBaseSquare f) n).comp
        (perfectSupportedUnionKMap j T n) =
      (perfectSupportedUnionKMap j' S n).comp
        (perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) n)
          := by
  ext x
  obtain ⟨y, rfl⟩ :=
    (boundedFlatPerfectSupportedToPerfectSupportedKMap_bijective (T ⊔ j.opensRange).ι n).surjective
      x
  have h₁ := DFunLike.congr_fun (boundedFlatPerfectSupportedUnionKMap_comparison j T n) y
  have h₂ := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat (qcSupportedBaseSquare
    f) n)
    (boundedFlatPerfectSupportedUnionKMap j T n y)
  change perfectSupportedKPullback (qcSupportedBaseSquare f) n
    (boundedFlatPerfectSupportedToPerfectSupportedKMap T.ι n
      (boundedFlatPerfectSupportedUnionKMap j T n y)) =
    boundedFlatPerfectSupportedToPerfectSupportedKMap S.ι n
      (boundedFlatPerfectSupportedKPullback f n
        (boundedFlatPerfectSupportedUnionKMap j T n y)) at h₂
  have h₃ := DFunLike.congr_fun
    (boundedFlatPerfectSupportedUnionKMap_pullback j' j f g w n) y
  have h₄ := DFunLike.congr_fun (boundedFlatPerfectSupportedUnionKMap_comparison j' S n)
    (boundedFlatPerfectSupportedKPullback (supportedPairUnionSquare j' j f g w) n y)
  have h₅ := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat
    (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) n) y
  change perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) n
    (boundedFlatPerfectSupportedToPerfectSupportedKMap (T ⊔ j.opensRange).ι n y) =
    boundedFlatPerfectSupportedToPerfectSupportedKMap (S ⊔ j'.opensRange).ι n
      (boundedFlatPerfectSupportedKPullback (supportedPairUnionSquare j' j f g w) n y) at h₅
  exact (congrArg (perfectSupportedKPullback (qcSupportedBaseSquare f) n) h₁).trans
    (h₂.trans ((congrArg (boundedFlatPerfectSupportedToPerfectSupportedKMap S.ι n) h₃).trans
      (h₄.symm.trans (congrArg (perfectSupportedUnionKMap j' S n) h₅.symm))))

variable [CompactSpace U'] [CompactSpace U]

lemma perfectSupportedKRestrict_pairPullback (n : ℕ) :
    (perfectSupportedKPullback (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w))
      n).comp
        (perfectSupportedKRestrict j T n) =
      (perfectSupportedKRestrict j' S n).comp
        (perfectSupportedKPullback (qcSupportedBaseSquare f) n) := by
  rw [← perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T n,
    ← perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j' S n]
  rw [← MonoidHom.comp_assoc, perfectSupportedOpenKRestrict_pullback j' j f g w n,
    MonoidHom.comp_assoc, perfectSupportedOpenKPullback_comp_changeWeak j' j f g w n,
    ← MonoidHom.comp_assoc]

end Quillen.PerfectComplexes

end
