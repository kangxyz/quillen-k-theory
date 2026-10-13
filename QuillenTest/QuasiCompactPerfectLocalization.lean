/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.Affine.QuasiCompactPerfectLocalizationNaturality
public import Mathlib.Data.ZMod.Basic

/-! # Original quasi-compact affine-open localization sequence consumers -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
universe u
namespace QuillenTest.QuasiCompactPerfectLocalization
variable (R : CommRingCat.{u}) (W : (Spec R).Opens)
  (hW : IsCompact (W : Set (Spec R)))

/-- The actual relative boundary is retained on every original relative class. -/
theorem original_relative_boundary (n : ℕ)
    (a : PerfectOpenK W.ι (n + 1)) :
    quasiCompactPerfectConnectingHom R W hW n
      (perfectOpenKRestrict W.ι (n + 1) a) =
    perfectOpenConnectingHom W.ι n a :=
  DFunLike.congr_fun (quasiCompactPerfectConnectingHom_comp_relative R W hW n) a

include hW in
/-- A base class vanishing on the original open has an actual supported preimage. -/
theorem actual_supported_preimage (n : ℕ) (x : PerfectK (Spec R) n)
    (hx : perfectKRestrict W.ι n x = 1) :
    ∃ a, perfectSupportedKMap W.ι n a = x := by
  have hm : x ∈ (perfectKRestrict W.ι n).ker := hx
  rw [← range_perfectSupportedKMap_eq_ker_quasiCompact_perfectKRestrict R W hW n] at hm
  exact hm

/-- A supported class dying on the base is the actual boundary of an open class. -/
theorem actual_open_boundary_preimage (n : ℕ)
    (a : PerfectSupportedK W.ι n)
    (ha : perfectSupportedKMap W.ι n a = 1) :
    ∃ x, quasiCompactPerfectConnectingHom R W hW n x = a := by
  have hm : a ∈ (perfectSupportedKMap W.ι n).ker := ha
  rw [← range_quasiCompactPerfectConnectingHom_eq_ker_perfectSupportedKMap R W hW n] at hm
  exact hm

/-- Vanishing of the actual positive boundary gives an original base preimage. -/
theorem actual_base_preimage (n : ℕ)
    (x : PerfectK W.toScheme (n + 1))
    (hx : quasiCompactPerfectConnectingHom R W hW n x = 1) :
    ∃ a, perfectKRestrict W.ι (n + 1) a = x := by
  have hm : x ∈ (quasiCompactPerfectConnectingHom R W hW n).ker := hx
  rw [← range_quasiCompact_perfectKRestrict_eq_ker_quasiCompactPerfectConnectingHom R W hW n] at hm
  exact hm

/-- The transported boundary is still the actual homotopy-fiber boundary. -/
theorem actual_fiber_boundary (n : ℕ)
    (x : PerfectK W.toScheme (n + 1)) :
    perfectSupportedFiberKMap W.ι n
      (quasiCompactPerfectConnectingHom R W hW n x) =
    Quillen.HomotopyFiber.connectingHom
      (Quillen.Waldhausen.Fibration.changeWeakMap
        (perfectOpenNested W.ι))
      (perfectOpenWeakWaldhausen W.ι).kBasepoint
      (perfectWaldhausen (Spec R)).kBasepoint
      (Quillen.Waldhausen.Fibration.changeWeakMap_basepoint
        (perfectOpenNested W.ι)) n
      ((quasiCompactPerfectOpenKEquiv R W hW n).symm x) :=
  perfectSupportedFiberKMap_connecting W.ι n _

/-- The empty open is included over a ring with zero divisors, at original K0. -/
theorem empty_open_K0_exact :
    (perfectSupportedKMap (⊥ : (Spec (CommRingCat.of (ZMod 6))).Opens).ι 0).range =
      (perfectKRestrict (⊥ : (Spec (CommRingCat.of (ZMod 6))).Opens).ι 0).ker :=
  range_perfectSupportedKMap_eq_ker_quasiCompact_perfectKRestrict _ _
    (by simp) 0

/-- The exact old relative boundary determines the new target boundary uniquely. -/
theorem actual_boundary_unique (n : ℕ)
    (δ : PerfectK W.toScheme (n+1) →* PerfectSupportedK W.ι n)
    (hδ : δ.comp (perfectOpenKRestrict W.ι (n+1)) = perfectOpenConnectingHom W.ι n) :
    δ = quasiCompactPerfectConnectingHom R W hW n :=
  quasiCompactPerfectConnectingHom_unique R W hW n δ hδ

/-- Arbitrary original geometric pair squares commute with the target-to-support boundary. -/
theorem actual_pair_boundary {S : CommRingCat.{u}} {V : (Spec S).Opens}
    (hV : IsCompact (V : Set (Spec S)))
    (f : affineOpenPair R W ⟶ affineOpenPair S V) (n : ℕ) :
    let : CompactSpace (affineOpenPair R W).obj.obj.left :=
      (show CompactSpace W.toScheme from isCompact_iff_compactSpace.mp hW)
    let : CompactSpace (affineOpenPair S V).obj.obj.left :=
      (show CompactSpace V.toScheme from isCompact_iff_compactSpace.mp hV)
    ∀ x : PerfectK V.toScheme (n+1),
      perfectSupportedKPullback f n (quasiCompactPerfectConnectingHom S V hV n x) =
        quasiCompactPerfectConnectingHom R W hW n (perfectKPullback f.hom.hom.left (n+1) x) := by
  let : CompactSpace (affineOpenPair R W).obj.obj.left :=
      (show CompactSpace W.toScheme from isCompact_iff_compactSpace.mp hW)
  let : CompactSpace (affineOpenPair S V).obj.obj.left :=
      (show CompactSpace V.toScheme from isCompact_iff_compactSpace.mp hV)
  dsimp only
  intro x
  have hh := quasiCompactPerfectConnectingHom_pullback hW hV f n
  dsimp only at hh
  exact DFunLike.congr_fun hh x

end QuillenTest.QuasiCompactPerfectLocalization
