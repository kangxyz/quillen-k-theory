/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.SmallChains
public import Tests.LocalCoefficientChains

/-!
# Consumers of genuine cover-small local chains

The regular coefficient tests retain arbitrary path-class monodromy. A concrete
open cover of the real line has two proper members, contains a constant simplex,
and fails to contain one explicit crossing simplex in either member.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Convexity
open scoped Simplicial

universe u v

namespace Quillen.Tests.LocalCoefficientSmallChains

open LocalCoefficients LocalCoefficientChains

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The small-chain inclusion is injective for regular path-class coefficients,
not just for a constant coefficient system. -/
example (U : ι → Set X) (b : X) (V : ModuleCat.{u} ℤ) (n : ℕ) :
    Function.Injective ((smallChainComplexInclusion U (regularSystem b V)).f n) :=
  smallModuleInclusion_injective U (regularSystem b V) ⦋n⦌

/-- A small one-simplex has the genuine transported first-face boundary. -/
theorem regular_one_simplex_boundary (U : ι → Set X) (b : X) (V : ModuleCat.{u} ℤ)
    (σ : CoverSmallSimplex U ⦋1⦌) :
    smallChainInclusion U (regularSystem b V) σ ≫
        (smallChainComplex U (regularSystem b V)).d 1 0 =
      restrictionTransport (regularSystem b V) σ.val (SimplexCategory.δ 0) ≫
          smallChainInclusion U (regularSystem b V)
            (restrictSmallSimplex U σ (SimplexCategory.δ 0)) -
        restrictionTransport (regularSystem b V) σ.val (SimplexCategory.δ 1) ≫
          smallChainInclusion U (regularSystem b V)
            (restrictSmallSimplex U σ (SimplexCategory.δ 1)) := by
  rw [smallChainInclusion_d]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- In the small first face, the original regular-system path label is
concatenated with the edge path, so it is not silently made constant. -/
theorem regular_small_face_generator (U : ι → Set X) (b : X) (V : ModuleCat.{u} ℤ)
    {n : ℕ} (σ : CoverSmallSimplex U ⦋n + 1⦌) (i : Fin (n + 2))
    (q : FundamentalGroupoid.mk b ⟶
      FundamentalGroupoid.mk (σ.val (StdSimplex.single 0))) :
    Sigma.ι (fun _ : FundamentalGroupoid.mk b ⟶
        FundamentalGroupoid.mk (σ.val (StdSimplex.single 0)) ↦ V) q ≫
      restrictionTransport (regularSystem b V) σ.val (SimplexCategory.δ i) ≫
        smallChainInclusion U (regularSystem b V)
          (restrictSmallSimplex U σ (SimplexCategory.δ i)) =
    Sigma.ι (fun _ : FundamentalGroupoid.mk b ⟶
        FundamentalGroupoid.mk
          (restrictSimplex σ.val (SimplexCategory.δ i) (StdSimplex.single 0)) ↦ V)
      (q ≫ Path.Homotopic.Quotient.mk
        ((PathConnectedSpace.somePath (StdSimplex.single 0)
          ((StdSimplex.single 0).map (SimplexCategory.δ i))).map σ.val.continuous)) ≫
      smallChainInclusion U (regularSystem b V)
        (restrictSmallSimplex U σ (SimplexCategory.δ i)) := by
  rw [← Category.assoc]
  exact congrArg (fun f ↦ f ≫ smallChainInclusion U (regularSystem b V)
      (restrictSmallSimplex U σ (SimplexCategory.δ i)))
    (regular_transport_generator b V q _)

/-- Boundary closure for an arbitrary local system on a genuinely chosen family. -/
example (U : ι → Set X) (A : System.{u, u} X) (i j : ℕ)
    {x : (singularChainComplex A).X i} (hx : x ∈ smallChainSubmodule U A i) :
    (singularChainComplex A).d i j x ∈ smallChainSubmodule U A j :=
  smallChainSubmodule_d_mem U A i j hx

/-- The full cover recovers the original complex with its original inclusion. -/
example (A : System.{u, u} X) :
    (fullCoverChainIso (fun _ : Unit ↦ (Set.univ : Set X)) A ⟨(), rfl⟩).hom =
      smallChainComplexInclusion (fun _ : Unit ↦ (Set.univ : Set X)) A := rfl

/-- A cover of the real line by two proper open intervals. -/
def intervalCover (i : Bool) : Set ℝ :=
  if i then Set.Ioi (-1) else Set.Iio 1

/-- Both members really are open. -/
theorem intervalCover_open (i : Bool) : IsOpen (intervalCover i) := by
  cases i
  · exact isOpen_Iio
  · exact isOpen_Ioi

/-- The two proper members cover the whole space. -/
theorem intervalCover_covers (x : ℝ) : ∃ i, x ∈ intervalCover i := by
  by_cases hx : x < 1
  · exact ⟨false, hx⟩
  · exact ⟨true, by change -1 < x; linarith⟩

/-- Neither member is the entire space. -/
theorem intervalCover_proper (i : Bool) : intervalCover i ≠ Set.univ := by
  cases i
  · intro h
    have : (1 : ℝ) ∈ intervalCover false := by rw [h]; trivial
    exact (lt_irrefl (1 : ℝ)) this
  · intro h
    have : (-1 : ℝ) ∈ intervalCover true := by rw [h]; trivial
    exact (lt_irrefl (-1 : ℝ)) this

/-- A concrete small simplex in every degree of this nontrivial open cover. -/
def zeroSimplex (n : SimplexCategory) : CoverSmallSimplex intervalCover n :=
  ⟨ContinuousMap.const _ 0, false, by
    rintro _ ⟨x, rfl⟩
    change (0 : ℝ) < 1
    norm_num⟩

/-- An explicit singular segment from -2 to 2, crossing the whole overlap. -/
def crossingSimplex : SingularSimplex ℝ ⦋1⦌ where
  toFun x := 4 * x.weights 1 - 2
  continuous_toFun := by fun_prop

/-- Cover-smallness is a genuine restriction even for this finite open cover. -/
theorem crossingSimplex_not_small : ¬ IsCoverSmall intervalCover crossingSimplex := by
  rintro ⟨i, hi⟩
  cases i
  · have h := hi ⟨StdSimplex.single 1, rfl⟩
    norm_num [crossingSimplex, intervalCover] at h
  · have h := hi ⟨StdSimplex.single 0, rfl⟩
    norm_num [crossingSimplex, intervalCover] at h

/-- The concrete cover and regular path-class coefficients instantiate the
original subcomplex inclusion, without assuming a quasi-isomorphism. -/
example (V : ModuleCat.{0} ℤ) (n : ℕ) :
    Mono ((smallChainComplexInclusion intervalCover (regularSystem (0 : ℝ) V)).f n) :=
  inferInstance

end Quillen.Tests.LocalCoefficientSmallChains
