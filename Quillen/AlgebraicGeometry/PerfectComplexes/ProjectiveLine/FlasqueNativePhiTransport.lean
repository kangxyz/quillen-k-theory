/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueGPhiMatrix

/-!
# Bijection transport to the original native affine two-summand K-map

The literal model inclusions and actual affine scheme inverse are bijective
on the original K-groups. Their already proved native-map comparison therefore
transports bijectivity in either direction, without asserting the open PhiG identity.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open Quillen.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands

lemma nativeInverse_KMap_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective (perfectKFlatPullback (nativeAffineIso R).inv n) := by
  let f := perfectKFlatPullback (nativeAffineIso R).inv n
  let g := perfectKFlatPullback (nativeAffineIso R).hom n
  have hgf : g.comp f = MonoidHom.id (PerfectK (twoChartLine R) n) := by
    dsimp only [g, f]
    rw [← perfectKFlatPullback_comp]
    simpa only [Iso.hom_inv_id] using (perfectKFlatPullback_id (twoChartLine R) n)
  have hfg : f.comp g = MonoidHom.id
      (PerfectK (nativeLineFunctor.obj (affineBase R)).obj n) := by
    dsimp only [g, f]
    rw [← perfectKFlatPullback_comp]
    simpa only [Iso.inv_hom_id] using
      (perfectKFlatPullback_id (nativeLineFunctor.obj (affineBase R)).obj n)
  constructor
  · intro a b h
    exact (DFunLike.congr_fun hgf a).symm.trans
      ((congrArg g h).trans (DFunLike.congr_fun hgf b))
  · intro y
    exact ⟨g y, DFunLike.congr_fun hfg y⟩

def modelPairToPerfectPair (R : CommRingCat.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (Spec R)).K n ×
      (FlasqueBoundedBelow.waldhausen (Spec R)).K n) :
    PerfectK (Spec R) n × PerfectK (Spec R) n :=
  (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)) n a.1,
    Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)) n a.2)

lemma modelPairToPerfectPair_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective (modelPairToPerfectPair R n) := by
  have hI := FlasqueBoundedBelow.perfectInclusion_KMap_bijective (Spec R) n
  constructor
  · intro a b h
    exact _root_.Prod.ext (hI.1 (congrArg _root_.Prod.fst h))
      (hI.1 (congrArg _root_.Prod.snd h))
  · rintro ⟨a, b⟩
    obtain ⟨x, hx⟩ := hI.2 a
    obtain ⟨y, hy⟩ := hI.2 b
    exact ⟨(x, y), _root_.Prod.ext hx hy⟩

/-- The existing original native affine map is bijective exactly when the actual model map is. -/
theorem PhiTwoSummandKMap_bijective_iff_native (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective (PhiTwoSummandKMap R n) ↔
      Function.Bijective (nativeTwoSummandKMap (affineBase R) n) := by
  let i := modelPairToPerfectPair R n
  let j := (perfectKFlatPullback (nativeAffineIso R).inv n).comp
    (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (twoChartLine R)) n)
  have hi : Function.Bijective i := modelPairToPerfectPair_bijective R n
  have hj : Function.Bijective j := (nativeInverse_KMap_bijective R n).comp
    (FlasqueBoundedBelow.perfectInclusion_KMap_bijective (twoChartLine R) n)
  have hc (x) : j (PhiTwoSummandKMap R n x) =
      nativeTwoSummandKMap (affineBase R) n (i x) :=
    PhiTwoSummandKMap_native R n x.1 x.2
  constructor
  · intro hPhi
    constructor
    · intro a b h
      obtain ⟨x, rfl⟩ := hi.2 a
      obtain ⟨y, rfl⟩ := hi.2 b
      exact congrArg i (hPhi.1 (hj.1 ((hc x).trans (h.trans (hc y).symm))))
    · intro y
      obtain ⟨z, hz⟩ := hj.2 y
      obtain ⟨x, hx⟩ := hPhi.2 z
      exact ⟨i x, (hc x).symm.trans ((congrArg j hx).trans hz)⟩
  · intro hNative
    constructor
    · intro a b h
      exact hi.1 (hNative.1 ((hc a).symm.trans ((congrArg j h).trans (hc b))))
    · intro y
      obtain ⟨z, hz⟩ := hNative.2 (j y)
      obtain ⟨x, hx⟩ := hi.2 z
      exact ⟨x, hj.1 ((hc x).trans
        ((congrArg (nativeTwoSummandKMap (affineBase R) n) hx).trans hz))⟩

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
