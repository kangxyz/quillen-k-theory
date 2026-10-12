/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassSeedNull
public import
Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedLaurentContractionNaturality

/-!
# Coefficient naturality of the original graded Bass seed null

The same chosen contraction and fixed original cone-null family commute with actual coefficient
maps. Evaluating their prescribed finite relative concatenation proves naturality of the literal
joint null, and hence of its curried loop-valued nullhomotopy. The private evaluation lemmas
retain both times through the original operations and endpoint casts. No replacement contraction,
supplied naturality hypothesis, or interchange with a localization null is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum

private theorem seed_comparison_cast_apply {E B : LoopPrespectrum.{u}} {f g : E ⟶ B}
    {H K H' K' : Homotopy f g} (hH : H = H') (hK : K = K')
    (e : H.RelHomotopy K = H'.RelHomotopy K') (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (cast e J).level n (r, (s, x)) = J.level n (r, (s, x)) := by
  subst hH
  subst hK
  rfl

private theorem seed_transRefl_eq_reparam {E B : LoopPrespectrum.{u}} {f g : E ⟶ B}
    (H : Homotopy f g) :
    H.trans (Homotopy.refl g) = H.reparam
      ⟨fun s ↦ ⟨Path.Homotopy.transReflReparamAux s,
        Path.Homotopy.transReflReparamAux_mem_I s⟩, by fun_prop⟩
      (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
      (Subtype.ext Path.Homotopy.transReflReparamAux_one) := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  have hp := Path.Homotopy.trans_refl_reparam (H.path n x)
  rw [← Homotopy.path_refl g n x, ← Homotopy.path_trans] at hp
  exact DFunLike.congr_fun hp s

section SeedEvaluation
variable {E B E' B' : LoopPrespectrum.{u}}
  {f g h : E ⟶ B} {f' g' h' : E' ⟶ B'}
  {n : ℕ} {x : E.space n} {x' : E'.space n} {p : B.space n → B'.space n}

private theorem seed_track_symm_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ s, H'.symm.level n (s, x') = p (H.symm.level n (s, x)) :=
  fun s ↦ hH (unitInterval.symm s)

private theorem seed_comparison_refl_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.refl H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.refl H).level n (r, (s, x))) := fun _ s ↦ hH s

private theorem seed_comparison_symm_natural
    {H K : Homotopy f g} {H' K' : Homotopy f' g'}
    {J : H.RelHomotopy K} {J' : H'.RelHomotopy K'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x)))) :
    ∀ r s, J'.symm.level n (r, (s, x')) = p (J.symm.level n (r, (s, x))) :=
  fun r s ↦ hJ (unitInterval.symm r) s

private theorem seed_comparison_trans_natural
    {H K L : Homotopy f g} {H' K' L' : Homotopy f' g'}
    {J : H.RelHomotopy K} {M : K.RelHomotopy L}
    {J' : H'.RelHomotopy K'} {M' : K'.RelHomotopy L'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x))))
    (hM : ∀ r s, M'.level n (r, (s, x')) = p (M.level n (r, (s, x)))) :
    ∀ r s, (J'.trans M').level n (r, (s, x')) =
      p ((J.trans M).level n (r, (s, x))) := by
  intro r s
  change ((J'.level n).trans (M'.level n)) (r, (s, x')) =
    p (((J.level n).trans (M.level n)) (r, (s, x)))
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hJ _ s
  · exact hM _ s

private theorem seed_comparison_hcomp_natural
    {H K : Homotopy f g} {L M : Homotopy g h}
    {H' K' : Homotopy f' g'} {L' M' : Homotopy g' h'}
    {J : H.RelHomotopy K} {N : L.RelHomotopy M}
    {J' : H'.RelHomotopy K'} {N' : L'.RelHomotopy M'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x))))
    (hN : ∀ r s, N'.level n (r, (s, x')) = p (N.level n (r, (s, x)))) :
    ∀ r s, (J'.hcomp N').level n (r, (s, x')) =
      p ((J.hcomp N).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.hcomp
  change (ContinuousMap.Homotopy.trans _ _) (s, (r, x')) =
    p ((ContinuousMap.Homotopy.trans _ _) (s, (r, x)))
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact hJ r _
  · exact hN r _

private theorem seed_comparison_transRefl_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.transRefl H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.transRefl H).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.transRefl
  simp only [eq_mp_eq_cast, seed_comparison_cast_apply, seed_transRefl_eq_reparam]
  exact hH _

private theorem seed_comparison_reflTransSymm_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.reflTransSymm H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.reflTransSymm H).level n (r, (s, x))) := by
  intro r s
  exact hH _

private theorem seed_comparison_reflTrans_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.reflTrans H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.reflTrans H).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.reflTrans
  simp only [eq_mp_eq_cast, seed_comparison_cast_apply,
    Homotopy.symm_trans, Homotopy.symm_refl, Homotopy.symm_symm]
  exact seed_comparison_transRefl_natural (seed_track_symm_natural hH) r (unitInterval.symm s)

private theorem seed_comparison_reflSymmTrans_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.reflSymmTrans H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.reflSymmTrans H).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.reflSymmTrans
  simp only [eq_mp_eq_cast, seed_comparison_cast_apply, Homotopy.symm_symm]
  exact seed_comparison_reflTransSymm_natural (seed_track_symm_natural hH) r s

end SeedEvaluation
end Quillen.LoopPrespectrum

namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- Actual coefficient maps preserve the prescribed joint null at both independent times. -/
theorem boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineFullOpenGradedSectionBassConeMap j f).map n
        ((boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison j a).level n
          (r, (s, x))) =
      (boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison j b).level n
        (r, (s, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x)) := by
  have hN : ∀ t, (boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j b).level n
      (t, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x) =
      (boundedFlatAffineFullOpenGradedSectionBassConeMap j f).map n
        ((boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j a).level n (t, x)) :=
    fun t ↦ (boundedFlatAffineFullOpenGradedSectionBassNullHomotopy_naturality_apply j f n t x).symm
  have hJ : ∀ r s,
      ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j b).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j b)))).level n
            (r, (s, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x)) =
      (boundedFlatAffineFullOpenGradedSectionBassConeMap j f).map n
        (((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).postcomp
          (mappingConeInclusion
            (StrictSquare.comparison
              (boundedFlatAffineFullOpenGradedSectionBassSquare j a)))).level n (r, (s, x))) := by
    intro r s
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j b))).map n
        ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j b).level n
          (r, (s, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j b))).map n
          (((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
            ((laurentUnderFunctor R).map f)).map n
              ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).level n
                (r, (s, x))))
    exact congrArg
      ((mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j b))).map n)
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction_naturality_apply
        j f n r s x).symm
  unfold boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison
  exact (seed_comparison_trans_natural
    (seed_comparison_hcomp_natural
      (seed_comparison_refl_natural (seed_track_symm_natural hN))
      (seed_comparison_trans_natural
        (seed_comparison_hcomp_natural hJ (seed_comparison_refl_natural hN))
        (seed_comparison_reflTrans_natural hN)))
    (seed_comparison_symm_natural (seed_comparison_reflSymmTrans_natural hN)) r s).symm

/-- Currying the same original joint null preserves its exact coefficient and null-time square. -/
theorem boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (r : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    (parameterLoopingMap (boundedFlatAffineFullOpenGradedSectionBassConeMap j f)).map n
        ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).level n (r, x)) =
      (boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j b).level n
        (r, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x) := by
  apply Path.ext
  funext s
  exact boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison_naturality_apply j f n r s x

end Quillen.PerfectComplexes
