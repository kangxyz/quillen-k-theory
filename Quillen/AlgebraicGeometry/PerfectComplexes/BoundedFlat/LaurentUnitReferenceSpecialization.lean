/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.LaurentUnitReferenceCore
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MChartSideRows

/-!
# The original unit-shifted positive chart-side attachment

The actual beta, total unit and C0 declarations are publicly imported from the lower owner.
The upper chart-side declarations retain their names, types, definitions and source indices.
Their additional MChartSideRows prerequisites remain visible; no C1 or mixed lift is asserted.
-/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.FunctorIdentityAutomorphism
universe u

namespace Quillen.PerfectComplexes.LaurentUnitReferenceSpecialization
open GlobalUnitReferenceNaturality BassH0Merge
variable {R : CommRingCat.{u}} (P : Over (Spec R))

variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The polynomial reference is the original positive C1 source-side reference. -/
abbrev polynomialReference := BassOverlap.projectionMap P (a := a) ≫
  BassMOuterJoin.sideBinarySource P p q

/-- The ordinary attachment is the original oldSideIso, with the actual projection equality. -/
def ordinaryAnchor : (BassOverlap.commonReference P p q).functor ≅
    (polynomialReference P p q ≫ normalizedMap (laurentPlus P c)).functor :=
  BassMOuterJoin.oldSideIso P p q (underToLaurent R) (laurentPlus_projection P c)

/-- The second attachment is shifted by the original total unit, not by a polynomial unit. -/
def shiftedAnchor : (BassOverlap.commonReference P p q).functor ≅
    (polynomialReference P p q ≫ normalizedMap (laurentPlus P c)).functor :=
  commonUnit P p q ≪≫ ordinaryAnchor P p q

/-- The fixed second attachment retains the actual target Laurent action on its whole reference. -/
theorem shiftedAnchor_eq_target_action :
    shiftedAnchor P p q = ordinaryAnchor P p q ≪≫
      onFunctor (polynomialReference P p q ≫ normalizedMap (laurentPlus P c)).functor
        (smallUnit P c) := by
  unfold shiftedAnchor
  rw [commonUnit_eq_action]
  exact reference_intertwine (op P, (laurentUnderFunctor R).obj c) (laurentUnit P c)
    (BassOverlap.commonReference P p q).functor
    (polynomialReference P p q ≫ normalizedMap (laurentPlus P c)).functor
    (ordinaryAnchor P p q)

/-- Preserve the full polynomial node before applying the actual positive chart. -/
def polynomialNode (i : Fin 3) :
    Σ F : modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (polynomialUnderFunctor R).obj c))),
      (polynomialReference P p q).functor ≅ F.functor :=
  ⟨BassOverlap.projectionMap P (a := a) ≫ (BassMOuterJoin.sideBinaryNodes P p q i).1,
    isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (BassMOuterJoin.sideBinaryNodes P p q i).2⟩

/-- Common-unit reanchoring of the original side is the complete shifted polynomial attachment.
This does not assert that any separately whiskered TenNodes family is that reanchoring. -/
theorem positive_side_shifted_node (i : Fin 3) :
    anchorNode (commonUnit P p q)
      (BassOverlap.chartOverlapNodes P p q (underToLaurent R) (laurentPlus_projection P c)
        (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i))) =
      BassH1Join.postReferenceNode (BassOverlap.commonReference P p q)
        (normalizedMap (laurentPlus P c)) (shiftedAnchor P p q) (polynomialNode P p q i) := by
  have h {V₀ W₀ V W : Model.{u + 1}} (F : V ⟶ W) (A : V ⟶ V₀) (J : W₀ ⟶ W)
      (H : V₀ ⟶ W₀) (D : Fin 3 → Σ G : V₀ ⟶ W₀, H.functor ≅ G.functor)
      (ρ : F.functor ≅ (A ≫ H ≫ J).functor) (τ : F.functor ≅ F.functor)
      (j : Fin 3) :
      anchorNode τ (BassH1Join.prePostNodes F A J H D ρ j) =
        BassH1Join.postReferenceNode F J (τ ≪≫ ρ)
          (⟨A ≫ (D j).1, isoWhiskerLeft A.functor (D j).2⟩ :
            Σ G : V ⟶ W₀, (A ≫ H).functor ≅ G.functor) := by
    have hf : (A ≫ (D j).1 ≫ J).functor = ((A ≫ (D j).1) ≫ J).functor := rfl
    apply Sigma.ext (Model.Hom.ext hf)
    apply heq_of_eq
    change τ ≪≫ (ρ ≪≫ isoWhiskerLeft A.functor (isoWhiskerRight (D j).2 J.functor)) =
      (τ ≪≫ ρ) ≪≫ isoWhiskerRight (isoWhiskerLeft A.functor (D j).2) J.functor
    rw [BassH1Join.whisker_iso_interchange, Iso.trans_assoc]
  rw [BassMOuterJoin.old_side_row]
  exact h (BassOverlap.commonReference P p q) (BassOverlap.projectionMap P (a := a))
    (normalizedMap (laurentPlus P c)) (BassMOuterJoin.sideBinarySource P p q)
    (BassMOuterJoin.sideBinaryNodes P p q) (ordinaryAnchor P p q) (commonUnit P p q) i

end Quillen.PerfectComplexes.LaurentUnitReferenceSpecialization
