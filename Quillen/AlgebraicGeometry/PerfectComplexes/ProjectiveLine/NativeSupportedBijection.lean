/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeInverseImageBoundary
public import Mathlib.Algebra.FiveLemma

/-! # Supported original native Phi from ambient bijectivity

The original connective localization rows, taken twice on the base, give
bijectivity of the literal inverse-image supported map from bijectivity of
the original ambient maps on the base and its compact open. The four ambient
hypotheses are explicit; this module does not prove them.
-/
@[expose] public section
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProjectiveLine

/-- The compact base open inherits quasi-separatedness through its actual open embedding. -/
instance nativeOpenBase_quasiSeparatedSpace (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (Z : X.obj.Opens) [CompactSpace Z.toScheme] :
    QuasiSeparatedSpace (nativeOpenBase X Z).obj := by
  change QuasiSeparatedSpace Z.toScheme
  exact Z.ι.isOpenEmbedding.quasiSeparatedSpace

end AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine

private theorem mulExact_prodMap {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) (h : Function.MulExact f g) :
    Function.MulExact (f.prodMap f) (g.prodMap g) := by
  rintro ⟨a, b⟩
  change (g a, g b) = (1, 1) ↔ ∃ x : A × A, (f x.1, f x.2) = (a, b)
  constructor
  · intro hab
    obtain ⟨x, hx⟩ := (h a).mp (congrArg Prod.fst hab)
    obtain ⟨y, hy⟩ := (h b).mp (congrArg Prod.snd hab)
    exact ⟨(x, y), Prod.ext hx hy⟩
  · rintro ⟨⟨x, y⟩, hxy⟩
    have hx : f x = a := congrArg Prod.fst hxy
    have hy : f y = b := congrArg Prod.snd hxy
    rw [← hx, ← hy]
    exact Prod.ext (h.apply_apply_eq_one x) (h.apply_apply_eq_one y)

variable (X : QuasiCompactSchemes.{u}) (Z : X.obj.Opens) [CompactSpace Z.toScheme]

/-- The original restriction square uses the actual inverse-image comparison. -/
theorem nativeTwoSummandKMap_preimageRestrict (n : ℕ) (a b : PerfectK X.obj n) :
    perfectKRestrict ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι n
        (nativeTwoSummandKMap X n (a, b)) =
      perfectKRestrict (nativeProjectionOpenIso X Z).inv n
        (nativeTwoSummandKMap (nativeOpenBase X Z) n
          (perfectKRestrict Z.ι n a, perfectKRestrict Z.ι n b)) := by
  have hcomp := perfectKRestrict_comp (nativeProjectionOpenIso X Z).inv
    (nativeLineFunctor.map (nativeOpenBaseInclusion X Z)).hom n
  simp only [nativeProjectionOpenIso_inv_inclusion] at hcomp
  rw [hcomp, MonoidHom.comp_apply]
  exact congrArg (perfectKRestrict (nativeProjectionOpenIso X Z).inv n)
    (nativeTwoSummandKMap_open (nativeOpenBaseInclusion X Z) n a b)

private theorem nativePreimageRestrict_bijective (n : ℕ) :
    Function.Bijective (perfectKRestrict (nativeProjectionOpenIso X Z).inv n) := by
  let e := nativeProjectionOpenIso X Z
  have hleft (x : PerfectK (nativeLineFunctor.obj (nativeOpenBase X Z)).obj n) :
      perfectKRestrict e.hom n (perfectKRestrict e.inv n x) = x := by
    change ((perfectKRestrict e.hom n).comp (perfectKRestrict e.inv n)) x = x
    rw [← perfectKRestrict_comp]
    simp only [e.hom_inv_id, perfectKRestrict_id, MonoidHom.id_apply]
  have hright (x : PerfectK ((nativeProjection.app X).hom ⁻¹ᵁ Z).toScheme n) :
      perfectKRestrict e.inv n (perfectKRestrict e.hom n x) = x := by
    change ((perfectKRestrict e.inv n).comp (perfectKRestrict e.hom n)) x = x
    rw [← perfectKRestrict_comp]
    simp only [e.inv_hom_id, perfectKRestrict_id, MonoidHom.id_apply]
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

variable [QuasiSeparatedSpace X.obj]

/-- The pinned group five lemma proves original supported Phi in degree `n`, including zero. -/
theorem nativeSupportedPreimageTwoSummandKMap_bijective_of_ambient_degrees (n : ℕ)
    (hXsucc : Function.Bijective (nativeTwoSummandKMap X (n + 1)))
    (hZsucc : Function.Bijective (nativeTwoSummandKMap (nativeOpenBase X Z) (n + 1)))
    (hX : Function.Bijective (nativeTwoSummandKMap X n))
    (hZ : Function.Bijective (nativeTwoSummandKMap (nativeOpenBase X Z) n)) :
    Function.Bijective (nativeSupportedPreimageTwoSummandKMap X Z n) := by
  let j := ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι
  let r := perfectKRestrict Z.ι (n + 1)
  let d := qcqsPerfectConnectingHom Z.ι n
  let s := perfectSupportedKMap Z.ι n
  let t := perfectKRestrict Z.ι n
  let rP := perfectKRestrict j (n + 1)
  let dP := qcqsPerfectConnectingHom j n
  let sP := perfectSupportedKMap j n
  let tP := perfectKRestrict j n
  let iZsucc := (perfectKRestrict (nativeProjectionOpenIso X Z).inv (n + 1)).comp
    (nativeTwoSummandKMap (nativeOpenBase X Z) (n + 1))
  let iZ := (perfectKRestrict (nativeProjectionOpenIso X Z).inv n).comp
    (nativeTwoSummandKMap (nativeOpenBase X Z) n)
  have hc₁ : rP.comp (nativeTwoSummandKMap X (n + 1)) =
      iZsucc.comp (r.prodMap r) := by
    ext x
    exact nativeTwoSummandKMap_preimageRestrict X Z (n + 1) x.1 x.2
  have hc₂ : dP.comp iZsucc =
      (nativeSupportedPreimageTwoSummandKMap X Z n).comp (d.prodMap d) := by
    ext x
    exact (nativeTwoSummandKMap_preimageConnecting X Z n x.1 x.2).symm
  have hc₃ : sP.comp (nativeSupportedPreimageTwoSummandKMap X Z n) =
      (nativeTwoSummandKMap X n).comp (s.prodMap s) := by
    ext x
    exact nativeSupportedPreimageTwoSummandKMap_forget X Z n x.1 x.2
  have hc₄ : tP.comp (nativeTwoSummandKMap X n) = iZ.comp (t.prodMap t) := by
    ext x
    exact nativeTwoSummandKMap_preimageRestrict X Z n x.1 x.2
  have hr : Function.MulExact r d :=
    MonoidHom.mulExact_iff.mpr
      (range_qcqs_perfectKRestrict_eq_ker_qcqsPerfectConnectingHom Z.ι n).symm
  have hd : Function.MulExact d s :=
    MonoidHom.mulExact_iff.mpr
      (range_qcqsPerfectConnectingHom_eq_ker_perfectSupportedKMap Z.ι n).symm
  have hs : Function.MulExact s t :=
    MonoidHom.mulExact_iff.mpr
      (range_perfectSupportedKMap_eq_ker_qcqs_perfectKRestrict Z.ι n).symm
  have hrP : Function.MulExact rP dP :=
    MonoidHom.mulExact_iff.mpr
      (range_qcqs_perfectKRestrict_eq_ker_qcqsPerfectConnectingHom j n).symm
  have hdP : Function.MulExact dP sP :=
    MonoidHom.mulExact_iff.mpr
      (range_qcqsPerfectConnectingHom_eq_ker_perfectSupportedKMap j n).symm
  have hsP : Function.MulExact sP tP :=
    MonoidHom.mulExact_iff.mpr
      (range_perfectSupportedKMap_eq_ker_qcqs_perfectKRestrict j n).symm
  have hiZsucc : Function.Bijective iZsucc :=
    (nativePreimageRestrict_bijective X Z (n + 1)).comp hZsucc
  have hiZ : Function.Bijective iZ :=
    (nativePreimageRestrict_bijective X Z n).comp hZ
  exact MonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (r.prodMap r) (d.prodMap d) (s.prodMap s) (t.prodMap t)
    rP dP sP tP (nativeTwoSummandKMap X (n + 1)) iZsucc
    (nativeSupportedPreimageTwoSummandKMap X Z n) (nativeTwoSummandKMap X n) iZ
    hc₁ hc₂ hc₃ hc₄ (mulExact_prodMap r d hr) (mulExact_prodMap d s hd)
    (mulExact_prodMap s t hs) hrP hdP hsP hXsucc.2 hiZsucc hX hiZ.1

/-- Ambient original Phi bijectivity on the base and its compact open suffices in every degree. -/
theorem nativeSupportedPreimageTwoSummandKMap_bijective_of_ambient
    (hX : ∀ k : ℕ, Function.Bijective (nativeTwoSummandKMap X k))
    (hZ : ∀ k : ℕ, Function.Bijective (nativeTwoSummandKMap (nativeOpenBase X Z) k))
    (n : ℕ) : Function.Bijective (nativeSupportedPreimageTwoSummandKMap X Z n) :=
  nativeSupportedPreimageTwoSummandKMap_bijective_of_ambient_degrees X Z n
    (hX (n + 1)) (hZ (n + 1)) (hX n) (hZ n)

end Quillen.PerfectComplexes.ProjectiveLine
