/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.BoundedComparison
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Triangulated properties from bounded complex terms

The original brutal-layer triangles and lower-cutoff inclusion propagate a triangulated
object property from single terms to a complex with explicit finite term bounds.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe v u v' u'
open Quillen.CochainComplex
open Quillen.Waldhausen.GilletWaldhausen
namespace HomotopyCategory.Plus
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (F : HomotopyCategory.Plus A ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
variable (P : ObjectProperty D) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [P.IsTriangulatedClosed₂]

/-- A finite downward induction through the actual brutal-layer triangles. -/
theorem property_obj_brutal_of_upper_bound (K : CochainComplex A ℤ) (b : ℤ)
    (hK : ∀ i, b < i → IsZero (K.X i))
    (hs : ∀ n, P (F.obj ((HomotopyCategory.Plus.quotient A).obj (singlePlus (K.X n) n))))
    (k : ℕ) :
    P (F.obj ((HomotopyCategory.Plus.quotient A).obj (brutalPlus K (b + 1 - k)))) := by
  induction k with
  | zero =>
    have hz := F.map_isZero ((HomotopyCategory.Plus.quotient A).map_isZero
      (brutalPlus_isZero K b (b + 1) hK (by omega)))
    simpa only [Nat.cast_zero, sub_zero] using P.prop_of_isZero hz
  | succ k ih =>
    apply P.ext_of_isTriangulatedClosed₂
      (F.mapTriangle.obj (brutalLayerTriangle K (b + 1 - (k + 1))))
      (F.map_distinguished _ (brutalLayerTriangle_distinguished K _))
    · change P (F.obj ((HomotopyCategory.Plus.quotient A).obj
        (brutalPlus K (b + 1 - ((k + 1 : ℕ) : ℤ) + 1))))
      have hn : b + 1 - ((k + 1 : ℕ) : ℤ) + 1 = b + 1 - (k : ℤ) := by omega
      rw [hn]
      exact ih
    · exact hs _

/-- A triangulated property of the images of all terms holds for an explicitly bounded complex. -/
theorem property_obj_of_term_bounds (K : _root_.CochainComplex.Plus A) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i))
    (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hs : ∀ n, P (F.obj ((HomotopyCategory.Plus.quotient A).obj
      (singlePlus (K.obj.X n) n)))) :
    P (F.obj ((HomotopyCategory.Plus.quotient A).obj K)) := by
  let m := min a (b + 1)
  have hi : IsIso (stupidTruncGEInclusion K.obj m) := by
    have (i : ℤ) : IsIso ((stupidTruncGEInclusion K.obj m).f i) := by
      by_cases hmi : m ≤ i
      · rw [stupidTruncGEInclusion_f_of_le K.obj m i hmi]
        infer_instance
      · exact (stupidTruncGE_isZero_X K.obj m i (by omega)).isIso
          (hl i ((lt_of_not_ge hmi).trans_le (min_le_left _ _))) _
    exact HomologicalComplex.Hom.isIso_of_components _
  let e : brutalPlus K.obj m ≅ K :=
    (_root_.CochainComplex.plus A).isoMk (asIso (stupidTruncGEInclusion K.obj m))
  apply P.prop_of_iso (F.mapIso ((HomotopyCategory.Plus.quotient A).mapIso e))
  have hm : b + 1 - ((b + 1 - m).toNat : ℤ) = m := by
    rw [Int.toNat_of_nonneg (by dsimp [m]; omega)]
    omega
  have h := property_obj_brutal_of_upper_bound F P K.obj b hu hs (b + 1 - m).toNat
  rwa [hm] at h
end HomotopyCategory.Plus
