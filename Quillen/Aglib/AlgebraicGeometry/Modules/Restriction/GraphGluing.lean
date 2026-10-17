/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.Overlap
public import Aglib.AlgebraicGeometry.Modules.Subobjects.Gluing
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-!
# Actual restriction graphs and compatible gluing

Chart maps into the original ambient product retain both projections. Compatible monic graph
data glue by the existing subobject construction, retaining the original local maps and exact
original hypotheses.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
namespace Quillen.PerfectComplexes.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
/-- A pair of chart maps into two ambient sheaves, viewed as a chart map
into their actual ambient product. -/
def restrictionGraph {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : U.Modules} {G M : X.Modules} (i : A ⟶ G.restrict j) (f : A ⟶ M.restrict j) :
    A ⟶ (G ⨯ M).restrict j :=
  prod.lift i f ≫ inv (prodComparison (Scheme.Modules.restrictFunctor j) G M)

@[reassoc (attr := simp)]
theorem restrictionGraph_fst {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : U.Modules} {G M : X.Modules} (i : A ⟶ G.restrict j) (f : A ⟶ M.restrict j) :
    restrictionGraph j i f ≫ (Scheme.Modules.restrictFunctor j).map prod.fst = i := by
  simp [restrictionGraph, Category.assoc, inv_prodComparison_map_fst]

@[reassoc (attr := simp)]
theorem restrictionGraph_snd {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : U.Modules} {G M : X.Modules} (i : A ⟶ G.restrict j) (f : A ⟶ M.restrict j) :
    restrictionGraph j i f ≫ (Scheme.Modules.restrictFunctor j).map prod.snd = f := by
  simp [restrictionGraph, Category.assoc, inv_prodComparison_map_snd]

instance restrictionGraph_mono {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : U.Modules} {G M : X.Modules} (i : A ⟶ G.restrict j) (f : A ⟶ M.restrict j)
    [Mono i] : Mono (restrictionGraph j i f) := by
  have : Mono (restrictionGraph j i f ≫ (Scheme.Modules.restrictFunctor j).map prod.fst) := by
    rw [restrictionGraph_fst]
    infer_instance
  exact mono_of_mono (restrictionGraph j i f)
    ((Scheme.Modules.restrictFunctor j).map (prod.fst : G ⨯ M ⟶ G))

/-- Compatible chart graph maps give an actual global source and morphism,
with both original chart maps retained by the supplied trivializations. -/
theorem exists_glued_graph_map {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k]
    {A : U.Modules} {B : V.Modules} {G M : X.Modules}
    (i : A ⟶ G.restrict j) (l : B ⟶ G.restrict k) [Mono i] [Mono l]
    (f : A ⟶ M.restrict j) (g : B ⟶ M.restrict k)
    (e : A.restrict (pullback.fst j k) ≅ B.restrict (pullback.snd j k))
    (hG : (Scheme.Modules.restrictFunctor (pullback.fst j k)).map i ≫
        (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app G =
      e.hom ≫ (Scheme.Modules.restrictFunctor (pullback.snd j k)).map l)
    (hM : (Scheme.Modules.restrictFunctor (pullback.fst j k)).map f ≫
        (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app M =
      e.hom ≫ (Scheme.Modules.restrictFunctor (pullback.snd j k)).map g) :
    ∃ (N : X.Modules) (h : N ⟶ M),
      ∃ (eU : N.restrict j ≅ A) (eV : N.restrict k ≅ B),
        (Scheme.Modules.restrictFunctor j).map h = eU.hom ≫ f ∧
        (Scheme.Modules.restrictFunctor k).map h = eV.hom ≫ g := by
  have hc : (Scheme.Modules.restrictFunctor (pullback.fst j k)).map
        (restrictionGraph j i f) ≫ (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j
          k).hom.app (G ⨯ M) =
      e.hom ≫ (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
        (restrictionGraph k l g) := by
    let F := Scheme.Modules.restrictFunctor k ⋙
      Scheme.Modules.restrictFunctor (pullback.snd j k)
    apply (cancel_mono (prodComparison F G M)).mp
    apply prod.hom_ext
    · simp only [Category.assoc, prodComparison_fst]
      change (Scheme.Modules.restrictFunctor (pullback.fst j k)).map
          (restrictionGraph j i f) ≫ (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j
            k).hom.app (G ⨯ M) ≫
          (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
            ((Scheme.Modules.restrictFunctor k).map prod.fst) = _
      have hn := (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.naturality
        (show G ⨯ M ⟶ G from prod.fst)
      dsimp only [Functor.comp_map] at hn
      dsimp only [F, Functor.comp_map]
      rw [← hn, ← Category.assoc, ← Functor.map_comp, restrictionGraph_fst]
      rw [← Functor.map_comp, restrictionGraph_fst]
      exact hG
    · simp only [Category.assoc, prodComparison_snd]
      change (Scheme.Modules.restrictFunctor (pullback.fst j k)).map
          (restrictionGraph j i f) ≫ (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j
            k).hom.app (G ⨯ M) ≫
          (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
            ((Scheme.Modules.restrictFunctor k).map prod.snd) = _
      have hn := (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.naturality
        (show G ⨯ M ⟶ M from prod.snd)
      dsimp only [Functor.comp_map] at hn
      dsimp only [F, Functor.comp_map]
      rw [← hn, ← Category.assoc, ← Functor.map_comp, restrictionGraph_snd]
      rw [← Functor.map_comp, restrictionGraph_snd]
      exact hM
  obtain ⟨N, h, _, eU, eV, hU, hV⟩ := AlgebraicGeometry.Scheme.Modules.exists_glued_subobject j k
    (restrictionGraph j i f) (restrictionGraph k l g) e hc
  refine ⟨N, h ≫ prod.snd, eU, eV, ?_, ?_⟩
  · rw [Functor.map_comp, hU, Category.assoc, restrictionGraph_snd]
  · rw [Functor.map_comp, hV, Category.assoc, restrictionGraph_snd]


end Quillen.PerfectComplexes.ProjectiveLine
end
end
