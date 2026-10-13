/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.WeakObjectCompositionCube
public import Quillen.Topology.Realization.Constant

/-! # Literal chosen-zero faces of the original weak-composition cube -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Convexity MonoidalCategory
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)

/-- Both entire vertex triangles are the actual degenerate chosen-zero simplex. -/
theorem weakObjectCompositionFamily_vertex (e : Fin 2) :
    (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) ⊗ₘ 𝟙 Δ[2]) ≫
        bisimplexFamily W (W.weakObjectCompositionPrism f g hf hg)
          (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) =
      SSet.const (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) := by
  ext n z
  apply Subtype.ext
  have hobj : ∀ p,
      ((((SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) ⊗ₘ 𝟙 Δ[2]) ≫
        bisimplexFamily W (W.weakObjectCompositionPrism f g hf hg)
          (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg)).app n) z).val.obj p =
        W.zero := by
    intro p
    change (W.weakObjectCompositionPrism f g hf hg).obj
      (z.2.down.toOrderHom p.1, interval e e le_rfl) = W.zero
    generalize z.2.down.toOrderHom p.1 = k
    fin_cases k <;> fin_cases e <;> rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q a
  have hz := W.isZero
  rw [← hobj p] at hz
  exact hz.eq_of_src _ _

/-- The whole nerve triangle stays at the literal basepoint on either object-edge endpoint. -/
theorem weakObjectCompositionRealization_vertex (e : Fin 2) (z : StdSimplex ℝ (Fin 3)) :
    W.weakObjectCompositionRealization f g hf hg (StdSimplex.single e, z) = W.kBasepoint := by
  have he : bisimplexFamily W
      (gridMap₂ (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) (𝟙 ⦋2⦌) ⋙
        W.weakObjectCompositionPrism f g hf hg)
      ((W.weakObjectCompositionPrism_isSimplex₂ f g hf hg).precomp W.cof W.weq
        (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) (𝟙 ⦋2⦌)) =
        SSet.const (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) := by
    rw [← bisimplexFamily_precomp]
    simpa using W.weakObjectCompositionFamily_vertex f g hf hg e
  have h := bisimplexRealization_precomp W (W.weakObjectCompositionPrism f g hf hg)
    (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg)
    (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) (𝟙 ⦋2⦌) (StdSimplex.single 0) z
  rw [bisimplexRealization_apply W
    (gridMap₂ (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) (𝟙 ⦋2⦌) ⋙
      W.weakObjectCompositionPrism f g hf hg), he, realization_const_apply] at h
  have hc : (ConcreteCategory.hom (SimplexCategory.const ⦋0⦌ ⦋1⦌ e)) 0 = e := rfl
  have hi : (⇑(ConcreteCategory.hom (𝟙 ⦋2⦌)) : Fin 3 → Fin 3) = id := rfl
  have hb : realizationPoint (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) =
      W.kBasepoint := by
    unfold realizationPoint kBasepoint basepoint
    exact congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm
      (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)))) (Subsingleton.elim _ _)
  rw [hb] at h
  change bisimplexRealization W (W.weakObjectCompositionPrism f g hf hg)
    (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) (StdSimplex.single e, z) =
      (W.kBasepoint : |sSet W.cof W.weq|)
  simpa only [StdSimplex.map_single, hc, hi, StdSimplex.map_id] using h

/-- Comparison and nerve time preserve the actual initial loop endpoint. -/
theorem weakObjectCompositionCube_loop_zero (r s : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (r, s, 0) = W.kBasepoint := by
  change W.weakObjectCompositionRealization f g hf hg (StdSimplex.homeomorphI.symm 0, _) = _
  rw [StdSimplex.homeomorphI_symm_zero, weakObjectCompositionRealization_vertex]

/-- Comparison and nerve time preserve the actual terminal loop endpoint. -/
theorem weakObjectCompositionCube_loop_one (r s : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (r, s, 1) = W.kBasepoint := by
  change W.weakObjectCompositionRealization f g hf hg (StdSimplex.homeomorphI.symm 1, _) = _
  rw [StdSimplex.homeomorphI_symm_one, weakObjectCompositionRealization_vertex]

/-- The specified cube is a jointly continuous square in the original based-loop space. -/
def weakObjectCompositionLoops :
    C(unitInterval × unitInterval, Path W.kBasepoint W.kBasepoint) where
  toFun z := {
    toFun t := W.weakObjectCompositionCube f g hf hg (z.1, z.2, t)
    continuous_toFun := by fun_prop
    source' := W.weakObjectCompositionCube_loop_zero f g hf hg z.1 z.2
    target' := W.weakObjectCompositionCube_loop_one f g hf hg z.1 z.2 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (W.weakObjectCompositionCube f g hf hg).continuous.comp
      ((continuous_fst.fst).prodMk ((continuous_fst.snd).prodMk continuous_snd))

/-- Every comparison, nerve and object-loop coordinate remains the originally specified one. -/
theorem weakObjectCompositionLoops_apply (r s t : unitInterval) :
    W.weakObjectCompositionLoops f g hf hg (r, s) t =
      W.weakObjectCompositionCube f g hf hg (r, s, t) := rfl

end Quillen.Waldhausen.Structure
