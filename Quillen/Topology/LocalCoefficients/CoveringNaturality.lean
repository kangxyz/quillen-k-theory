/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.CoveringChains
public import Quillen.Topology.LocalCoefficients.RegularFunctoriality

/-!
# The original-map square for regular covering chains

A supplied commuting square of actual covering maps induces a commuting
square between regular twisted chains and ordinary chains of the covers.
The lower map is the original map between total spaces, and the upper map
is the existing pushforward preceded by the actual path-class coefficient
map. The corner basepoint equality is explicit.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Convexity Opposite
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {E B E' B' : Type u}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
variable {p : E → B} {p' : E' → B'} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
variable [SimplyConnectedSpace E] [SimplyConnectedSpace E']
variable (k : C(E, E')) (f : C(B, B')) (h : ∀ e, p' (k e) = f (p e))

/-- The regular-basis equivalence respects the original maps of a covering square. -/
theorem coveringRegularSimplexEquiv_map (e₀ : E) {n : SimplexCategory}
    (s : RegularSimplex (p e₀) n) :
    coveringRegularSimplexEquiv hp' (k e₀) n
        (mapRegularSimplex f (p e₀) (p' (k e₀)) (h e₀) s) =
      k.comp (coveringRegularSimplexEquiv hp e₀ n s) := by
  rw [coveringRegularSimplexEquiv_apply, coveringRegularSimplexEquiv_apply]
  apply (Covering.eq_lift hp' _ _ _ _ ?_ ?_).symm
  · change (Covering.projection hp').comp
      (k.comp (Covering.lift hp s.1 _ _)) = f.comp s.1
    rw [Covering.map_lift hp hp' k f h, Covering.projection_lift]
  · change k (Covering.lift hp s.1 _ _ (StdSimplex.single 0)) =
      (hp'.monodromy ((s.2.map f).cast (h e₀) rfl) ⟨k e₀, rfl⟩).1
    rw [Covering.lift_vertex]
    exact (Covering.monodromy_naturality_basepoint hp hp' k f h e₀ s.2).symm

/-- Degreewise naturality uses the original coefficient and spatial maps. -/
@[reassoc]
theorem coveringModuleIso_map (e₀ : E) (n : SimplexCategory) :
    regularPushforwardModuleMap f (p e₀) (p' (k e₀)) (h e₀) n ≫
        (coveringModuleIso hp' (k e₀) n).hom =
      (coveringModuleIso hp e₀ n).hom ≫
        pushforwardModuleMap k (constant E' integralCoefficients) n := by
  apply Sigma.hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro q z
  change (coveringModuleIso hp' (k e₀) n).hom
      (regularPushforwardModuleMap f (p e₀) (p' (k e₀)) (h e₀) n
        (regularChainGenerator (p e₀) ⟨σ, q⟩ z)) =
    pushforwardModuleMap k (constant E' integralCoefficients) n
      ((coveringModuleIso hp e₀ n).hom (regularChainGenerator (p e₀) ⟨σ, q⟩ z))
  simp [coveringRegularSimplexEquiv_map hp hp' k f h]

/-- The original-map square commutes before taking alternating faces. -/
@[reassoc]
theorem coveringSimplicialIso_map (e₀ : E) :
    regularPushforwardSimplicialMap f (p e₀) (p' (k e₀)) (h e₀) ≫
        (coveringSimplicialIso hp' (k e₀)).hom =
      (coveringSimplicialIso hp e₀).hom ≫
        pushforwardSimplicialMap k (constant E' integralCoefficients) := by
  ext n : 1
  exact coveringModuleIso_map hp hp' k f h e₀ n.unop

/-- The comparison intertwines genuine chain maps, retaining the original covering square. -/
@[reassoc]
theorem coveringConstantChainIso_map (e₀ : E) :
    regularPushforwardChainMap f (p e₀) (p' (k e₀)) (h e₀) ≫
        (coveringConstantChainIso hp' (k e₀)).hom =
      (coveringConstantChainIso hp e₀).hom ≫
        pushforwardChainMap k (constant E' integralCoefficients) := by
  have he := congrArg (fun η ↦ (AlgebraicTopology.alternatingFaceMapComplex
    (ModuleCat.{u} ℤ)).map η) (coveringSimplicialIso_map hp hp' k f h e₀)
  simpa [regularPushforwardChainMap_eq, coveringConstantChainIso,
    pushforwardChainMap] using he

/-- The final comparison square uses mathlib's ordinary singular-chain map of the original `k`. -/
@[reassoc]
theorem coveringChainIso_map (e₀ : E) :
    regularPushforwardChainMap f (p e₀) (p' (k e₀)) (h e₀) ≫
        (coveringChainIso hp' (k e₀)).hom =
      (coveringChainIso hp e₀).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
          integralCoefficients).map (TopCat.ofHom k) := by
  simp only [coveringChainIso, Iso.trans_hom, ← Category.assoc]
  rw [coveringConstantChainIso_map hp hp' k f h]
  simp only [Category.assoc, constantChainComplexIso_naturality]

end Quillen.LocalCoefficients
