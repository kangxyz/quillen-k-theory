/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ConnectingNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairPullback

/-!
# Naturality of the original supported/relative perfect boundary

The genuine bounded-flat boundary square and the literal inclusion comparisons
prove the square for the existing perfect K-pullback maps on qc ambient pairs.
Every commutative open-pair square is allowed; cartesianness and flatness are
unnecessary. The degree-zero supported boundary is included.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {A B : Quillen.Scheme.QuasiCompactOpenPairs.{u}}

/-- The unchanged original relative-to-supported boundary is natural under
arbitrary open-pair pullback between qc ambient schemes. -/
theorem perfectOpenConnectingHom_pullback (f : A ⟶ B) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (perfectOpenConnectingHom B.obj.obj.hom n) =
    (perfectOpenConnectingHom A.obj.obj.hom n).comp (perfectOpenKPullback f (n+1)) := by
  ext x
  obtain ⟨y, rfl⟩ := (boundedFlatPerfectOpenToPerfectOpenKMap_bijective B.obj.obj.hom
    (n+1)).surjective x
  have hB := DFunLike.congr_fun (boundedFlatPerfectOpenConnectingHom_comparison B.obj.obj.hom n) y
  have hS := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat f n)
    (boundedFlatPerfectOpenConnectingHom B.obj.obj.hom n y)
  have hF := DFunLike.congr_fun (boundedFlatPerfectOpenConnectingHom_pullback f.hom n) y
  have hA := DFunLike.congr_fun (boundedFlatPerfectOpenConnectingHom_comparison A.obj.obj.hom n)
    (boundedFlatPerfectOpenKPullback f.hom (n+1) y)
  have hO := DFunLike.congr_fun (perfectOpenKPullback_comp_boundedFlat f (n+1)) y
  simp only [MonoidHom.comp_apply] at hB hS hF hA hO ⊢
  rw [← hB, hS, hF, hA, hO]

/-- The original connecting homomorphisms form a natural transformation. -/
def perfectOpenConnectingNatTrans (n : ℕ) :
    PerfectOpenKFunctor.{u} (n+1) ⟶ PerfectSupportedKFunctor.{u} n where
  app X := GrpCat.ofHom (perfectOpenConnectingHom X.unop.obj.obj.hom n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (perfectOpenConnectingHom_pullback f.unop n).symm

@[simp]
theorem perfectOpenConnectingNatTrans_app (n : ℕ)
    (X : Quillen.Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ) :
    ((perfectOpenConnectingNatTrans n).app X).hom =
      perfectOpenConnectingHom X.unop.obj.obj.hom n := rfl

/-- All three original arrows in the supported/relative perfect sequence commute
with the same geometric pair pullback, including the boundary into K₀. -/
theorem perfectOpen_longExactSequence_pullback (f : A ⟶ B) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (perfectOpenConnectingHom B.obj.obj.hom n) =
      (perfectOpenConnectingHom A.obj.obj.hom n).comp (perfectOpenKPullback f (n+1)) ∧
    (perfectKPullback f.hom.hom.right n).comp (perfectSupportedKMap B.obj.obj.hom n) =
      (perfectSupportedKMap A.obj.obj.hom n).comp (perfectSupportedKPullback f n) ∧
    (perfectOpenKPullback f n).comp (perfectOpenKMap B.obj.obj.hom n) =
      (perfectOpenKMap A.obj.obj.hom n).comp (perfectKPullback f.hom.hom.right n) :=
  ⟨perfectOpenConnectingHom_pullback f n, perfectSupportedKMap_pullback f n,
    perfectOpenKMap_pullback f n⟩

end Quillen.PerfectComplexes
