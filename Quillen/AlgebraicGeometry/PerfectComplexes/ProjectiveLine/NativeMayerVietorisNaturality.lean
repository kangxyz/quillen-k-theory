/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenFunctorMayerVietoris
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeMayerVietorisGeometry

/-! # Original native Phi and the original two-open Mayer-Vietoris arrows -/
@[expose] public section

open Quillen.PerfectComplexes.OpenFunctorNaturality
open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeMayerVietoris
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine Waldhausen
  OpenFunctorNaturality

/-- Equality of the original geometric arrows preserves their original restriction K-map. -/
theorem restrictK_congr {A B : Scheme.{u}} {i j : A ⟶ B}
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i = j) (n : ℕ) :
    perfectKRestrict i n = perfectKRestrict j n := by
  subst j
  rfl

variable {V X : QuasiCompactSchemes.{u}} (f : V ⟶ X) [IsOpenImmersion f.hom]
  [QuasiSeparatedSpace X.obj] (T : X.obj.Opens) [CompactSpace T.toScheme]

/-- Original native Phi on the first open, through the canonical actual open comparison. -/
def onT (n : ℕ) : PerfectK T.toScheme n × PerfectK T.toScheme n →*
    PerfectK (lineT T).toScheme n :=
  (perfectKRestrict (nativeProjectionOpenIso X T).inv n).comp
    (nativeTwoSummandKMap (nativeOpenBase X T) n)

/-- Original native Phi on the overlap, through its canonical actual comparison. -/
def onOverlap (n : ℕ) : PerfectK (f.hom ⁻¹ᵁ T).toScheme n ×
    PerfectK (f.hom ⁻¹ᵁ T).toScheme n →* PerfectK (lineOverlap f T).toScheme n :=
  (perfectKRestrict (overlapIso f T).inv n).comp
    (nativeTwoSummandKMap (overlapBase f T) n)

omit [QuasiSeparatedSpace X.obj] in
/-- The first restriction square retains the original actual native maps. -/
theorem restrictT (n : ℕ) (a b : PerfectK X.obj n) :
    perfectKRestrict (lineT T).ι n (nativeTwoSummandKMap X n (a, b)) =
      onT T n (perfectKRestrict T.ι n a, perfectKRestrict T.ι n b) := by
  have h := congrArg (perfectKRestrict (nativeProjectionOpenIso X T).inv n)
    (nativeTwoSummandKMap_open (nativeOpenBaseInclusion X T) n a b)
  change ((perfectKRestrict (nativeProjectionOpenIso X T).inv n).comp
    (perfectKRestrict (nativeLineFunctor.map (nativeOpenBaseInclusion X T)).hom n))
      (nativeTwoSummandKMap X n (a, b)) = _ at h
  rw [← perfectKRestrict_comp] at h
  rw [restrictK_congr (nativeProjectionOpenIso_inv_inclusion X T) n] at h
  exact h

/-- The overlap restriction from the first open retains the T-first original resLE map. -/
theorem overlapFromT (n : ℕ) (a b : PerfectK T.toScheme n) :
    perfectKRestrict ((lineOpen f).resLE (lineT T) (lineOverlap f T) le_rfl) n
        (onT T n (a, b)) =
      onOverlap f T n (perfectKRestrict (overlapToT f T).hom n a,
        perfectKRestrict (overlapToT f T).hom n b) := by
  have h := congrArg (perfectKRestrict (overlapIso f T).inv n)
    (nativeTwoSummandKMap_open (overlapToT f T) n a b)
  change ((perfectKRestrict (overlapIso f T).inv n).comp
    (perfectKRestrict (nativeLineFunctor.map (overlapToT f T)).hom n))
      (nativeTwoSummandKMap (nativeOpenBase X T) n (a, b)) = _ at h
  rw [← perfectKRestrict_comp] at h
  change ((perfectKRestrict ((lineOpen f).resLE (lineT T) (lineOverlap f T) le_rfl) n).comp
    (perfectKRestrict (nativeProjectionOpenIso X T).inv n))
      (nativeTwoSummandKMap (nativeOpenBase X T) n (a, b)) = _
  rw [← perfectKRestrict_comp]
  rw [restrictK_congr (overlap_toT_inv f T) n]
  exact h

omit [IsOpenImmersion f.hom] in
/-- The overlap restriction from the second open retains the original inclusion. -/
theorem overlapFromV (n : ℕ) (a b : PerfectK V.obj n) :
    perfectKRestrict (lineOverlap f T).ι n (nativeTwoSummandKMap V n (a, b)) =
      onOverlap f T n (perfectKRestrict (f.hom ⁻¹ᵁ T).ι n a,
        perfectKRestrict (f.hom ⁻¹ᵁ T).ι n b) := by
  have h := congrArg (perfectKRestrict (overlapIso f T).inv n)
    (nativeTwoSummandKMap_open (overlapToV f T) n a b)
  change ((perfectKRestrict (overlapIso f T).inv n).comp
    (perfectKRestrict (nativeLineFunctor.map (overlapToV f T)).hom n))
      (nativeTwoSummandKMap V n (a, b)) = _ at h
  rw [← perfectKRestrict_comp] at h
  rw [restrictK_congr (overlapIso_inv_inclusion f T) n] at h
  exact h

/-- The first exact localization square on the actual target overlap. -/
def firstOverlapSquare :
    ExactRestrictionSquare (f.hom ⁻¹ᵁ T).ι (lineOverlap f T).ι :=
  (nativeFirstRestrictionSquare (overlapToV f T)).reindexTargetOpen
    (overlapIso f T).symm (lineOverlap f T).ι (overlapIso_inv_inclusion f T)

/-- The original left-tensor localization square on the actual target overlap. -/
def secondOverlapSquare :
    ExactRestrictionSquare (f.hom ⁻¹ᵁ T).ι (lineOverlap f T).ι :=
  (nativeSecondRestrictionSquare (overlapToV f T)).reindexTargetOpen
    (overlapIso f T).symm (lineOverlap f T).ι (overlapIso_inv_inclusion f T)

variable [QuasiSeparatedSpace V.obj]

/-- Original Phi commutes with the original excision-defined Mayer-Vietoris boundary. -/
theorem connecting (hc : ∀ x : X.obj, x ∈ Set.range f.hom ∨ x ∈ T)
    (n : ℕ) (a b : PerfectK (f.hom ⁻¹ᵁ T).toScheme (n + 1)) :
    nativeTwoSummandKMap X n
        (PerfectMayerVietoris.connectingHom f.hom T hc n a,
          PerfectMayerVietoris.connectingHom f.hom T hc n b) =
      PerfectMayerVietoris.connectingHom (lineOpen f) (lineT T) (line_cover f T hc) n
        (onOverlap f T (n + 1) (a, b)) := by
  have h₁ := connectingHom_natural f.hom (lineOpen f) T (lineT T)
    (nativeFirstPreimageSquare X T) (firstOverlapSquare f T)
    (nativeFirstSummandOpenIso f) hc (line_cover f T hc) n a
  have h₂ := connectingHom_natural f.hom (lineOpen f) T (lineT T)
    (nativeSecondPreimageSquare X T) (secondOverlapSquare f T)
    (nativeSecondSummandOpenIso f) hc (line_cover f T hc) n b
  change KMap (nativeFirstSummand_exact X) n
      (PerfectMayerVietoris.connectingHom f.hom T hc n a) =
    PerfectMayerVietoris.connectingHom (lineOpen f) (lineT T) (line_cover f T hc) n
      (KMap ((nativeFirstSummand_exact (overlapBase f T)).comp
        (perfectRestrict_waldhausenExact (overlapIso f T).inv)) (n + 1) a) at h₁
  change KMap (nativeSecondSummand_exact X) n
      (PerfectMayerVietoris.connectingHom f.hom T hc n b) =
    PerfectMayerVietoris.connectingHom (lineOpen f) (lineT T) (line_cover f T hc) n
      (KMap ((nativeSecondSummand_exact (overlapBase f T)).comp
        (perfectRestrict_waldhausenExact (overlapIso f T).inv)) (n + 1) b) at h₂
  rw [← KMap_comp_KMap (nativeFirstSummand_exact (overlapBase f T))
    (perfectRestrict_waldhausenExact (overlapIso f T).inv) (n + 1)] at h₁
  rw [← KMap_comp_KMap (nativeSecondSummand_exact (overlapBase f T))
    (perfectRestrict_waldhausenExact (overlapIso f T).inv) (n + 1)] at h₂
  change nativeTwoSummandKMap X n (_, _) =
    PerfectMayerVietoris.connectingHom (lineOpen f) (lineT T) (line_cover f T hc) n
      (perfectKRestrict (overlapIso f T).inv (n + 1)
        (nativeTwoSummandKMap (overlapBase f T) (n + 1) (a, b)))
  rw [nativeTwoSummandKMap_apply, nativeTwoSummandKMap_apply, map_mul, map_mul]
  exact congrArg₂ (· * ·) h₁ h₂

end Quillen.PerfectComplexes.ProjectiveLine.NativeMayerVietoris
