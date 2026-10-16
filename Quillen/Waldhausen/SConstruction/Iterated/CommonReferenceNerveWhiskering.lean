/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveParameter
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceWhiskering

/-!
# Actual common-reference node maps and whole-family whiskering

Pre- and postcomposition retain each complete dependent node in its original insertion order.
The actual nerve characteristic map is natural under those node maps. Its finite prespectrum
family is the original whiskered family at the unchanged parameter, including level zero.
No equality between distinct isomorphic nodes or product comparison with the whole nerve is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Convexity
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.IteratedS

namespace ModelSimplex
variable {V W T : Model.{u}}

/-- Postcomposition retains every original vertex and its specified reference isomorphism. -/
theorem ofIsos_postcomp {k : ℕ} (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (F i).functor) (J : W ⟶ T) :
    (ofIsos F₀ F ρ).postcomp J =
      ofIsos (F₀ ≫ J) (fun i ↦ F i ≫ J) (fun i ↦ isoWhiskerRight (ρ i) J.functor) := by
  apply ext_diagram
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  apply heq_of_eq
  change whiskerRight ((ρ i).inv ≫ (ρ j).hom) J.functor =
    whiskerRight (ρ i).inv J.functor ≫ whiskerRight (ρ j).hom J.functor
  exact whiskerRight_comp _ _ _

end ModelSimplex
namespace CommonReferenceNerve
variable {V W T V' W' : Model.{u}} {F : V ⟶ W} {G : V' ⟶ W'}

/-- A function of complete dependent nodes induces its actual map on nerve realizations. -/
def mapParameter (f : Node F → Node G) :
    C(|nerve (Codiscrete (Node F))|, |nerve (Codiscrete (Node G))|) :=
  (SSet.toTop.map (nerveMap (Codiscrete.functorOfFun f))).hom

/-- Every entire original simplex parameter follows the same full-node function. -/
theorem mapParameter_parameter (f : Node F → Node G) {k : ℕ}
    (N : Fin (k + 1) → Node F) (z : StdSimplex ℝ (Fin (k + 1))) :
    mapParameter f (parameter F N z) = parameter G (fun i ↦ f (N i)) z := by
  have he : SSet.yonedaEquiv.symm (Codiscrete.functor N) ≫
      nerveMap (Codiscrete.functorOfFun f) =
        SSet.yonedaEquiv.symm (Codiscrete.functor (fun i ↦ f (N i))) := by
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
    rfl
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (Codiscrete.functor N)) ≫
    SSet.toTop.map (nerveMap (Codiscrete.functorOfFun f)))
      ((SimplexCategory.toTopHomeo ⦋k⦌).symm z) = _
  rw [← Functor.map_comp, he]
  rfl

/-- Precompose the exact model morphism and its exact specified reference transformation. -/
def precompNode (J : T ⟶ V) (N : Node F) : Node (J ≫ F) :=
  ⟨J ≫ N.1, isoWhiskerLeft J.functor N.2⟩

/-- Postcompose the exact model morphism and its exact specified reference transformation. -/
def postcompNode (J : W ⟶ T) (N : Node F) : Node (F ≫ J) :=
  ⟨N.1 ≫ J, isoWhiskerRight N.2 J.functor⟩

/-- Whole finite families retain the original parameter under original precomposition. -/
theorem prespectrumFamily_precomp {k : ℕ} (N : Fin (k + 1) → Node F)
    (J : T ⟶ V) (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (prespectrum T).space n) :
    prespectrumFamily (J ≫ F) (fun i ↦ precompNode J (N i)) n (z, x) =
      prespectrumFamily F N n (z, (prespectrumMap J).map n x) := by
  rw [prespectrumFamily_eq, prespectrumFamily_eq]
  change prespectrumSimplexFamily
    (ModelSimplex.ofIsos (J ≫ F) (fun i ↦ J ≫ (N i).1)
      (fun i ↦ isoWhiskerLeft J.functor (N i).2)) n (z, x) = _
  rw [← ModelSimplex.ofIsos_precomp]
  exact prespectrumSimplexFamily_precomp _ J n z x

/-- Whole finite families retain the original parameter under original postcomposition. -/
theorem prespectrumFamily_postcomp {k : ℕ} (N : Fin (k + 1) → Node F)
    (J : W ⟶ T) (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (prespectrum V).space n) :
    prespectrumFamily (F ≫ J) (fun i ↦ postcompNode J (N i)) n (z, x) =
      (prespectrumMap J).map n (prespectrumFamily F N n (z, x)) := by
  rw [prespectrumFamily_eq, prespectrumFamily_eq]
  change prespectrumSimplexFamily
    (ModelSimplex.ofIsos (F ≫ J) (fun i ↦ (N i).1 ≫ J)
      (fun i ↦ isoWhiskerRight (N i).2 J.functor)) n (z, x) = _
  rw [← ModelSimplex.ofIsos_postcomp]
  exact prespectrumSimplexFamily_postcomp _ J n z x

end CommonReferenceNerve
end Quillen.Waldhausen.IteratedS
