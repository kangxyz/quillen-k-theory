/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexFaces
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumCompositionHomotopy

/-!
# Simplex Prespectrum

Convex third-parameter fillings in the original prespectrum simplex family.
The geometric Bass application must still identify its chosen surfaces inside one such family.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} {k : ℕ} (S : ModelSimplex V W k)

/-- The original entire simplex in finite barycentric coordinates. -/
def stageSimplexBarycentric (n : ℕ) :
    C(StdSimplex ℝ (Fin (k + 1)) × stageSpace n V, stageSpace n W) :=
  ⟨fun z ↦ stageSimplexRealization n S
    (z.2, (SimplexCategory.toTopHomeo ⦋k⦌).symm z.1), by fun_prop⟩

/-- The original loop-space level evaluates the higher family at a separate loop coordinate. -/
def simplexLoopFamily :
    C(StdSimplex ℝ (Fin (k + 1)) × Path (stagePoint 0 V) (stagePoint 0 V),
      Path (stagePoint 0 W) (stagePoint 0 W)) where
  toFun z := {
    toFun t := stageSimplexBarycentric S 0 (z.1, z.2 t)
    continuous_toFun := by fun_prop
    source' := by
      rw [Path.source]
      exact stageSimplexRealization_fixed_point 0 S _
    target' := by
      rw [Path.target]
      exact stageSimplexRealization_fixed_point 0 S _ }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z :
      (StdSimplex ℝ (Fin (k + 1)) × Path (stagePoint 0 V) (stagePoint 0 V)) × unitInterval ↦
      stageSimplexBarycentric S 0 (z.1.1, z.1.2 z.2))
    fun_prop

/-- The entire original prespectrum carries the same simplex family, including level zero. -/
def prespectrumSimplexFamily (n : ℕ) :
    C(StdSimplex ℝ (Fin (k + 1)) × (prespectrum V).space n, (prespectrum W).space n) :=
  Nat.casesOn n (simplexLoopFamily S) (stageSimplexBarycentric S)

/-- The higher family fixes the actual original point at every prespectrum level. -/
theorem prespectrumSimplexFamily_point (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) :
    prespectrumSimplexFamily S n (z, (prespectrum V).point n) = (prespectrum W).point n := by
  cases n with
  | zero =>
    apply Path.ext
    funext t
    exact stageSimplexRealization_fixed_point 0 S _
  | succ n => exact stageSimplexRealization_fixed_point n S _

/-- No simplex parameter is identified with the independent original structure coordinate. -/
theorem prespectrumSimplexFamily_structure (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (prespectrum V).space n) (t : unitInterval) :
    prespectrumSimplexFamily S (n + 1) (z, (prespectrum V).structureMap n x t) =
      (prespectrum W).structureMap n (prespectrumSimplexFamily S n (z, x)) t := by
  cases n with
  | zero => rfl
  | succ n => exact stageSimplexRealization_structure n S _ t x

/-- Level-zero evaluation keeps the original loop time separate from the whole simplex. -/
theorem prespectrumSimplexFamily_zero_apply (z : StdSimplex ℝ (Fin (k + 1)))
    (x : Path (stagePoint 0 V) (stagePoint 0 V)) (t : unitInterval) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      prespectrumSimplexFamily S 0 (z, x)) t = stageSimplexBarycentric S 0 (z, x t) := rfl

end Quillen.Waldhausen.IteratedS
namespace Quillen

/-- Pointwise convex interpolation of two arbitrary continuous simplex-valued parameter maps. -/
def simplexParameterInterpolation {T : Type*} [TopologicalSpace T] {k : ℕ}
    (p q : C(T, StdSimplex ℝ (Fin (k + 1)))) : C(unitInterval × T, StdSimplex ℝ (Fin (k + 1))) where
  toFun z := convexCombPair (R := ℝ) (unitInterval.symm z.1) z.1
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) (p z.2) (q z.2)
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (k + 1))).continuous_iff]
    unfold Function.comp
    refine continuous_pi (fun i ↦ ?_)
    simp only [unitInterval.coe_symm_eq, StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop

@[simp] theorem simplexParameterInterpolation_zero {T : Type*} [TopologicalSpace T] {k : ℕ}
    (p q : C(T, StdSimplex ℝ (Fin (k + 1)))) (x : T) :
    simplexParameterInterpolation p q (0, x) = p x := by simp [simplexParameterInterpolation]

@[simp] theorem simplexParameterInterpolation_one {T : Type*} [TopologicalSpace T] {k : ℕ}
    (p q : C(T, StdSimplex ℝ (Fin (k + 1)))) (x : T) :
    simplexParameterInterpolation p q (1, x) = q x := by simp [simplexParameterInterpolation]

/-- Every coincident boundary value remains exactly fixed throughout the third parameter. -/
theorem simplexParameterInterpolation_fixed {T : Type*} [TopologicalSpace T] {k : ℕ}
    (p q : C(T, StdSimplex ℝ (Fin (k + 1)))) (x : T) (hx : p x = q x) (r : unitInterval) :
    simplexParameterInterpolation p q (r, x) = p x := by
  simp [simplexParameterInterpolation, hx]

/-- The whole boundary of a square in its two original independent parameters. -/
def parameterSquareBoundary : Set (unitInterval × unitInterval) :=
  {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1}

/-- Any two relative path homotopies in one finite simplex have an actual filling fixing all
four square edges. This is the extra dimension beyond ordinary triangle composition. -/
def simplexPathHomotopyComparison {k : ℕ} {a b : StdSimplex ℝ (Fin (k + 1))}
    {p q : Path a b} (J K : p.Homotopy q) :
    J.toContinuousMap.HomotopyRel K.toContinuousMap parameterSquareBoundary where
  toFun := simplexParameterInterpolation J.toContinuousMap K.toContinuousMap
  continuous_toFun := (simplexParameterInterpolation J.toContinuousMap K.toContinuousMap).continuous
  map_zero_left := simplexParameterInterpolation_zero _ _
  map_one_left := simplexParameterInterpolation_one _ _
  prop' r z hz := by
    refine simplexParameterInterpolation_fixed J.toContinuousMap K.toContinuousMap z ?_ r
    change z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1 at hz
    rcases hz with h | h | h | h
    · rcases z with ⟨s, t⟩
      change s = 0 at h
      subst s
      exact (J.apply_zero t).trans (K.apply_zero t).symm
    · rcases z with ⟨s, t⟩
      change s = 1 at h
      subst s
      exact (J.apply_one t).trans (K.apply_one t).symm
    · rcases z with ⟨s, t⟩
      change t = 0 at h
      subst t
      exact (J.eq_fst s (by simp)).trans (K.eq_fst s (by simp)).symm
    · rcases z with ⟨s, t⟩
      change t = 1 at h
      subst t
      exact (J.eq_fst s (by simp)).trans (K.eq_fst s (by simp)).symm

end Quillen
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} {k : ℕ} (S : ModelSimplex V W k)
  {a b : StdSimplex ℝ (Fin (k + 1))} {p q : Path a b} (J K : p.Homotopy q)

/-- A concrete whole third-parameter family in the original prespectrum, preserving all four
specified square edges. The Bass application still has to identify its original lifted surfaces. -/
def prespectrumSimplexCube (n : ℕ) :
    C(unitInterval × (unitInterval × (unitInterval × (prespectrum V).space n)),
      (prespectrum W).space n) :=
  ⟨fun z ↦ prespectrumSimplexFamily S n
    (simplexPathHomotopyComparison J K (z.1, (z.2.1, z.2.2.1)), z.2.2.2), by fun_prop⟩

/-- The first entire square face is the original specified first parameter surface. -/
theorem prespectrumSimplexCube_zero (n : ℕ) (s t : unitInterval)
    (x : (prespectrum V).space n) :
    prespectrumSimplexCube S J K n (0, (s, (t, x))) =
      prespectrumSimplexFamily S n (J (s, t), x) := by
  change prespectrumSimplexFamily S n (simplexPathHomotopyComparison J K (0, (s, t)), x) = _
  rw [(simplexPathHomotopyComparison J K).apply_zero]
  rfl

/-- The final entire square face is the original specified second parameter surface. -/
theorem prespectrumSimplexCube_one (n : ℕ) (s t : unitInterval)
    (x : (prespectrum V).space n) :
    prespectrumSimplexCube S J K n (1, (s, (t, x))) =
      prespectrumSimplexFamily S n (K (s, t), x) := by
  change prespectrumSimplexFamily S n (simplexPathHomotopyComparison J K (1, (s, t)), x) = _
  rw [(simplexPathHomotopyComparison J K).apply_one]
  rfl

/-- All four original square-edge tracks are retained at every value of the new time. -/
theorem prespectrumSimplexCube_boundary (n : ℕ) (r s t : unitInterval)
    (x : (prespectrum V).space n) (h : (s, t) ∈ parameterSquareBoundary) :
    prespectrumSimplexCube S J K n (r, (s, (t, x))) =
      prespectrumSimplexFamily S n (J (s, t), x) := by
  change prespectrumSimplexFamily S n (simplexPathHomotopyComparison J K (r, (s, t)), x) = _
  rw [(simplexPathHomotopyComparison J K).eq_fst r h]
  rfl

/-- The original basepoint is fixed throughout all three geometric parameters. -/
theorem prespectrumSimplexCube_point (n : ℕ) (r s t : unitInterval) :
    prespectrumSimplexCube S J K n (r, (s, (t, (prespectrum V).point n))) =
      (prespectrum W).point n :=
  prespectrumSimplexFamily_point S n _

/-- The new third time remains independent of the original structure time. -/
theorem prespectrumSimplexCube_structure (n : ℕ) (r s t z : unitInterval)
    (x : (prespectrum V).space n) :
    prespectrumSimplexCube S J K (n + 1) (r, (s, (t, (prespectrum V).structureMap n x z))) =
      (prespectrum W).structureMap n (prespectrumSimplexCube S J K n (r, (s, (t, x)))) z :=
  prespectrumSimplexFamily_structure S n _ x z

end Quillen.Waldhausen.IteratedS
