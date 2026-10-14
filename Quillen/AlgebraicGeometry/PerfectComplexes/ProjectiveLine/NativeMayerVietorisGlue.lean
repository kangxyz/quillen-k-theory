/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeMayerVietorisNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeIsoInvariance
public import Mathlib.Algebra.FiveLemma

/-! # Binary two-open closure for the original native projective-line K-map

The five-term slice is local-pair(n+1), overlap(n+1), global(n), local-pair(n),
overlap(n). The genuine final local-pair K0 position supplies its right end
when n = 0. No surjectivity onto overlap K0 or negative boundary is used.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeMayerVietoris
open Quillen.Scheme Quillen.Scheme.ProjectiveLine

/-- Explicit rearrangement of the two original T-first local pairs into pairs of coefficients. -/
def localPairShuffle (A : Type u) (B : Type v) [Group A] [Group B] :
    (A × B) × (A × B) ≃* (A × A) × (B × B) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Two copies of an actual exact group row remain exact. -/
theorem mulExact_prodMap {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) (h : Function.MulExact f g) :
    Function.MulExact (f.prodMap f) (g.prodMap g) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (h x.1).mp (congrArg _root_.Prod.fst hx)
    obtain ⟨b, hb⟩ := (h x.2).mp (congrArg _root_.Prod.snd hx)
    exact ⟨(a, b), Prod.ext ha hb⟩
  · rintro ⟨a, rfl⟩
    exact Prod.ext (h.apply_apply_eq_one a.1) (h.apply_apply_eq_one a.2)

variable {V X : QuasiCompactSchemes.{u}} (f : V ⟶ X) [IsOpenImmersion f.hom]
  [QuasiSeparatedSpace X.obj] (T : X.obj.Opens) [CompactSpace T.toScheme]

variable [QuasiSeparatedSpace V.obj]

/-- The two original local Phi maps after the explicit T-first coefficient rearrangement. -/
def onLocalPair (n : ℕ) :
    (PerfectK T.toScheme n × PerfectK V.obj n) ×
        (PerfectK T.toScheme n × PerfectK V.obj n) →*
      PerfectK (lineT T).toScheme n × PerfectK (nativeLineFunctor.obj V).obj n :=
  ((onT T n).prodMap (nativeTwoSummandKMap V n)).comp
    (localPairShuffle (PerfectK T.toScheme n) (PerfectK V.obj n)).toMonoidHom

omit [QuasiSeparatedSpace X.obj] [QuasiSeparatedSpace V.obj] in
/-- Original restriction pairs commute with original Phi and the explicit coefficient rearrangement.
-/
theorem restrictionPair_square (n : ℕ) :
    (PerfectMayerVietoris.restrictionPair (lineOpen f) (lineT T) n).comp
        (nativeTwoSummandKMap X n) =
      (onLocalPair (V := V) T n).comp
        ((PerfectMayerVietoris.restrictionPair f.hom T n).prodMap
          (PerfectMayerVietoris.restrictionPair f.hom T n)) := by
  apply MonoidHom.ext
  intro a
  obtain ⟨a, b⟩ := a
  apply Prod.ext
  · exact restrictT T n a b
  · exact nativeTwoSummandKMap_open f n a b

omit [QuasiSeparatedSpace V.obj] in
/-- The actual T-first difference square has the unchanged first-times-inverse-second sign. -/
theorem overlapDifference_square (n : ℕ) :
    (PerfectMayerVietoris.overlapDifference (lineOpen f) (lineT T) n).comp
        (onLocalPair (V := V) T n) =
      (onOverlap f T n).comp
        ((PerfectMayerVietoris.overlapDifference f.hom T n).prodMap
          (PerfectMayerVietoris.overlapDifference f.hom T n)) := by
  ext a
  obtain ⟨⟨aT, aV⟩, ⟨bT, bV⟩⟩ := a
  change perfectKRestrict ((lineOpen f).resLE (lineT T) (lineOverlap f T) le_rfl) n
      (onT T n (aT, bT)) *
        (perfectKRestrict (lineOverlap f T).ι n (nativeTwoSummandKMap V n (aV, bV)))⁻¹ =
    onOverlap f T n
      (perfectKRestrict (f.hom.resLE T (f.hom ⁻¹ᵁ T) le_rfl) n aT *
          (perfectKRestrict (f.hom ⁻¹ᵁ T).ι n aV)⁻¹,
        perfectKRestrict (f.hom.resLE T (f.hom ⁻¹ᵁ T) le_rfl) n bT *
          (perfectKRestrict (f.hom ⁻¹ᵁ T).ι n bV)⁻¹)
  rw [overlapFromT, overlapFromV]
  exact (map_mul (onOverlap f T n)
    (perfectKRestrict (overlapToT f T).hom n aT,
      perfectKRestrict (overlapToT f T).hom n bT)
    ((perfectKRestrict (f.hom ⁻¹ᵁ T).ι n aV,
      perfectKRestrict (f.hom ⁻¹ᵁ T).ι n bV)⁻¹)).trans
        (congrArg₂ (· * ·) rfl (map_inv (onOverlap f T n) _)) |>.symm

variable (hc : ∀ x : X.obj, x ∈ Set.range f.hom ∨ x ∈ T)

/-- The original connecting square, as a homomorphism identity on the two source rows. -/
theorem connecting_square (n : ℕ) :
    (PerfectMayerVietoris.connectingHom (lineOpen f) (lineT T) (line_cover f T hc) n).comp
        (onOverlap f T (n + 1)) =
      (nativeTwoSummandKMap X n).comp
        ((PerfectMayerVietoris.connectingHom f.hom T hc n).prodMap
          (PerfectMayerVietoris.connectingHom f.hom T hc n)) := by
  ext a
  exact (connecting f T hc n a.1 a.2).symm

/-- The original three exact positions of the selected five-term slice, including n = 0. -/
theorem fiveTerm_exact (n : ℕ) :
    Function.MulExact (PerfectMayerVietoris.overlapDifference f.hom T (n + 1))
        (PerfectMayerVietoris.connectingHom f.hom T hc n) ∧
      Function.MulExact (PerfectMayerVietoris.connectingHom f.hom T hc n)
        (PerfectMayerVietoris.restrictionPair f.hom T n) ∧
      Function.MulExact (PerfectMayerVietoris.restrictionPair f.hom T n)
        (PerfectMayerVietoris.overlapDifference f.hom T n) := by
  let hT : IsCompact (T : Set X.obj) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T.toScheme))
  have h := PerfectMayerVietoris.qcqs_positiveExactSequence f.hom T hT hc n
  refine ⟨MonoidHom.mulExact_iff.mpr h.2.1.symm, MonoidHom.mulExact_iff.mpr h.2.2.symm, ?_⟩
  apply MonoidHom.mulExact_iff.mpr
  cases n with
  | zero => exact (PerfectMayerVietoris.qcqs_completeZeroTail f.hom T hT hc).2.2.symm
  | succ n => exact (PerfectMayerVietoris.qcqs_positiveExactSequence f.hom T hT hc n).1.symm

omit hc [QuasiSeparatedSpace X.obj] in
/-- The first local vertical map is bijective precisely from actual Phi on the first open. -/
theorem onT_bijective (n : ℕ)
    (hT : Function.Bijective (nativeTwoSummandKMap (nativeOpenBase X T) n)) :
    Function.Bijective (onT T n) :=
  (perfectKRestrictIsoEquiv (nativeProjectionOpenIso X T).symm n).bijective.comp hT

omit hc [IsOpenImmersion f.hom] [QuasiSeparatedSpace V.obj] in
/-- The overlap vertical map is bijective from actual Phi on the original overlap scheme. -/
theorem onOverlap_bijective (n : ℕ)
    (hW : Function.Bijective (nativeTwoSummandKMap (overlapBase f T) n)) :
    Function.Bijective (onOverlap f T n) :=
  (perfectKRestrictIsoEquiv (overlapIso f T).symm n).bijective.comp hW

omit hc [QuasiSeparatedSpace X.obj] [QuasiSeparatedSpace V.obj] in
/-- Explicit coefficient rearrangement preserves bijectivity of the two original local maps. -/
theorem onLocalPair_bijective (n : ℕ)
    (hT : Function.Bijective (nativeTwoSummandKMap (nativeOpenBase X T) n))
    (hV : Function.Bijective (nativeTwoSummandKMap V n)) :
    Function.Bijective (onLocalPair (V := V) T n) := by
  have hT' := onT_bijective T n hT
  have hprod : Function.Bijective ((onT T n).prodMap (nativeTwoSummandKMap V n)) := by
    constructor
    · intro a b h
      exact Prod.ext (hT'.1 (congrArg _root_.Prod.fst h))
        (hV.1 (congrArg _root_.Prod.snd h))
    · rintro ⟨a, b⟩
      obtain ⟨a', ha⟩ := hT'.2 a
      obtain ⟨b', hb⟩ := hV.2 b
      exact ⟨(a', b'), Prod.ext ha hb⟩
  exact hprod.comp (localPairShuffle (PerfectK T.toScheme n) (PerfectK V.obj n)).bijective

include hc in
/-- The original five-term ladder gives actual Phi bijectivity on a compact two-open union. -/
theorem bijective_of_cover
    (hT : ∀ n : ℕ, Function.Bijective (nativeTwoSummandKMap (nativeOpenBase X T) n))
    (hV : ∀ n : ℕ, Function.Bijective (nativeTwoSummandKMap V n))
    (hW : ∀ n : ℕ, Function.Bijective (nativeTwoSummandKMap (overlapBase f T) n))
    (n : ℕ) : Function.Bijective (nativeTwoSummandKMap X n) := by
  have hs := fiveTerm_exact f T hc n
  have ht := fiveTerm_exact (nativeLineFunctor.map f) (lineT T) (line_cover f T hc) n
  exact MonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    ((PerfectMayerVietoris.overlapDifference f.hom T (n + 1)).prodMap
      (PerfectMayerVietoris.overlapDifference f.hom T (n + 1)))
    ((PerfectMayerVietoris.connectingHom f.hom T hc n).prodMap
      (PerfectMayerVietoris.connectingHom f.hom T hc n))
    ((PerfectMayerVietoris.restrictionPair f.hom T n).prodMap
      (PerfectMayerVietoris.restrictionPair f.hom T n))
    ((PerfectMayerVietoris.overlapDifference f.hom T n).prodMap
      (PerfectMayerVietoris.overlapDifference f.hom T n))
    (PerfectMayerVietoris.overlapDifference (lineOpen f) (lineT T) (n + 1))
    (PerfectMayerVietoris.connectingHom (lineOpen f) (lineT T) (line_cover f T hc) n)
    (PerfectMayerVietoris.restrictionPair (lineOpen f) (lineT T) n)
    (PerfectMayerVietoris.overlapDifference (lineOpen f) (lineT T) n)
    (onLocalPair (V := V) T (n + 1)) (onOverlap f T (n + 1)) (nativeTwoSummandKMap X n)
    (onLocalPair (V := V) T n) (onOverlap f T n)
    (overlapDifference_square f T (n + 1)) (connecting_square f T hc n)
    (restrictionPair_square f T n) (overlapDifference_square f T n)
    (mulExact_prodMap _ _ hs.1) (mulExact_prodMap _ _ hs.2.1)
    (mulExact_prodMap _ _ hs.2.2) ht.1 ht.2.1 ht.2.2
    (onLocalPair_bijective (V := V) T (n + 1) (hT (n + 1)) (hV (n + 1))).2
    (onOverlap_bijective f T (n + 1) (hW (n + 1)))
    (onLocalPair_bijective (V := V) T n (hT n) (hV n)) (onOverlap_bijective f T n (hW n)).1

end Quillen.PerfectComplexes.ProjectiveLine.NativeMayerVietoris
