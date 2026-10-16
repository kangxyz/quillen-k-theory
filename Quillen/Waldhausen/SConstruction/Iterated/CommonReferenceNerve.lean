/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceFaces
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexPrespectrum
public import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# The actual common-reference nerve family

Every node retains its exact zero-preserving model morphism and its specified reference
isomorphism. The existing finite simplex family factors through the nerve of these nodes.
Realization uses only the original finite-simplex product comparison. No product comparison
with the whole nerve, higher filler, or compatibility of different chosen faces is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Opposite MonoidalCategory Convexity
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve
variable {V W : Model.{u}} (F₀ : V ⟶ W)

/-- A full original node, including the specified reference isomorphism. -/
abbrev Node := Σ F : V ⟶ W, F₀.functor ≅ F.functor

/-- The reference isomorphisms determine the actual transformation on every nerve arrow. -/
def diagram : Codiscrete (Node F₀) ⥤ (V ⥤ W) where
  obj i := i.as.1.functor
  map {i j} _ := i.as.2.inv ≫ j.as.2.hom
  map_id i := by simp
  map_comp f g := by simp [Category.assoc]

/-- Every original nerve chain is its exact common-reference model simplex. -/
def chain {k : ℕ} (c : Fin (k + 1) ⥤ Codiscrete (Node F₀)) : ModelSimplex V W k :=
  ModelSimplex.ofIsos F₀ (fun i ↦ (c.obj i).as.1) (fun i ↦ (c.obj i).as.2)

/-- The simplex diagram is literally the original chain followed by the reference diagram. -/
theorem chain_diagram {k : ℕ} (c : Fin (k + 1) ⥤ Codiscrete (Node F₀)) :
    (chain F₀ c).diagram = c ⋙ diagram F₀ := rfl

/-- Reindexing the nerve chain preserves the whole original simplex face. -/
theorem chain_face {k l : ℕ} (c : Fin (k + 1) ⥤ Codiscrete (Node F₀))
    (α : ⦋l⦌ ⟶ ⦋k⦌) :
    chain F₀ (α.toOrderHom.monotone.functor ⋙ c) = (chain F₀ c).face α := by
  apply ModelSimplex.ext_diagram
  rfl

/-- The actual nerve simplex of a full original node list; its labels need no global order. -/
def simplexMap {k : ℕ} (N : Fin (k + 1) → Node F₀) :
    Δ[k] ⟶ nerve (Codiscrete (Node F₀)) :=
  SSet.yonedaEquiv.symm (Codiscrete.functor N)

/-- Every nerve coordinate retains the entire original dependent node. -/
theorem simplexMap_obj {k : ℕ} (N : Fin (k + 1) → Node F₀)
    (n : SimplexCategoryᵒᵖ) (τ : (Δ[k]).obj n) (i : Fin (n.unop.len + 1)) :
    (((simplexMap F₀ N).app n τ).obj i).as = N (τ.down.toOrderHom i) := rfl

/-- The actual simplicial family on all chains of the common-reference category. -/
def stageTransformation (r : ℕ) :
    (stages r).obj V ⊗ nerve (Codiscrete (Node F₀)) ⟶ (stages r).obj W where
  app n := ↾fun z ↦ stageSimplexFunction r (chain F₀ z.2) n z.1 ⟨𝟙 n.unop⟩
  naturality n m α := by
    ext z : 3
    symm
    change ((stages r).obj W).map α
        (stageSimplexFunction r (chain F₀ z.2) n z.1 ⟨𝟙 n.unop⟩) = _
    rw [stageSimplexFunction_naturality]
    change stageSimplexFunction r (chain F₀ z.2) m
        (((stages r).obj V).map α z.1) ⟨α.unop ≫ 𝟙 n.unop⟩ =
      stageSimplexFunction r
        (chain F₀ (α.unop.toOrderHom.monotone.functor ⋙ z.2)) m
        (((stages r).obj V).map α z.1) ⟨𝟙 m.unop⟩
    have h := stageSimplexFunction_face r (chain F₀ z.2) α.unop m
      (((stages r).obj V).map α z.1) ⟨𝟙 m.unop⟩
    simpa only [Category.id_comp, Category.comp_id, ← chain_face] using h

/-- The original finite simplex is exactly the restriction of the nerve family. -/
theorem stageTransformation_factorization (r : ℕ) {k : ℕ}
    (N : Fin (k + 1) → Node F₀) :
    (stages r).obj V ◁ simplexMap F₀ N ≫ stageTransformation F₀ r =
      stageTransformationSimplex r
        (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)) := by
  ext n z : 4
  change stageSimplexFunction r (chain F₀ ((simplexMap F₀ N).app n z.2))
      n z.1 ⟨𝟙 n.unop⟩ =
    stageSimplexFunction r
      (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)) n z.1 z.2
  have hc : chain F₀ ((simplexMap F₀ N).app n z.2) =
      (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)).face z.2.down := by
    apply ModelSimplex.ext_diagram
    rfl
  rw [hc]
  have h := stageSimplexFunction_face r
    (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2))
    z.2.down n z.1 ⟨𝟙 n.unop⟩
  have he : (⟨𝟙 n.unop ≫ z.2.down⟩ : (Δ[k]).obj n) = z.2 := by
    apply ULift.ext
    exact Category.id_comp _
  rw [he] at h
  exact h.symm

/-- Realize the nerve factorization through the unchanged finite-simplex product map. -/
def stageRealization (r : ℕ) {k : ℕ} (N : Fin (k + 1) → Node F₀) :
    C(stageSpace r V × |(Δ[k] : SSet.{u})|, stageSpace r W) :=
  (SSet.toTop.map (stageTransformation F₀ r)).hom.comp
    ((SSet.toTop.map ((stages r).obj V ◁ simplexMap F₀ N)).hom.comp
      (realizationProductSimplexIso ((stages r).obj V) k).inv.hom)

/-- The realized factorization is the same whole original finite-simplex map. -/
theorem stageRealization_eq (r : ℕ) {k : ℕ} (N : Fin (k + 1) → Node F₀) :
    stageRealization F₀ r N = stageSimplexRealization r
      (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)) := by
  ext z
  change (SSet.toTop.map ((stages r).obj V ◁ simplexMap F₀ N) ≫
    SSet.toTop.map (stageTransformation F₀ r))
      ((realizationProductSimplexIso ((stages r).obj V) k).inv z) = _
  rw [← Functor.map_comp, stageTransformation_factorization]
  rfl

/-- Barycentric coordinates pass through the actual original realization homeomorphism. -/
def stageBarycentric (r : ℕ) {k : ℕ} (N : Fin (k + 1) → Node F₀) :
    C(StdSimplex ℝ (Fin (k + 1)) × stageSpace r V, stageSpace r W) :=
  ⟨fun z ↦ stageRealization F₀ r N (z.2, (SimplexCategory.toTopHomeo ⦋k⦌).symm z.1),
    by fun_prop⟩

/-- The full original barycentric family, without reparametrization. -/
theorem stageBarycentric_eq (r : ℕ) {k : ℕ} (N : Fin (k + 1) → Node F₀) :
    stageBarycentric F₀ r N = stageSimplexBarycentric
      (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)) r := by
  ext z
  exact congrArg (fun f ↦ f (z.2, (SimplexCategory.toTopHomeo ⦋k⦌).symm z.1))
    (stageRealization_eq F₀ r N)

/-- The nerve factorization fixes the same original zero point for every parameter. -/
theorem stageBarycentric_point (r : ℕ) {k : ℕ} (N : Fin (k + 1) → Node F₀)
    (z : StdSimplex ℝ (Fin (k + 1))) :
    stageBarycentric F₀ r N (z, stagePoint r V) = stagePoint r W := by
  rw [stageBarycentric_eq]
  exact stageSimplexRealization_fixed_point r _ _

/-- The original input loop is evaluated at a separate coordinate after nerve factorization. -/
def loopFamily {k : ℕ} (N : Fin (k + 1) → Node F₀) :
    C(StdSimplex ℝ (Fin (k + 1)) × Path (stagePoint 0 V) (stagePoint 0 V),
      Path (stagePoint 0 W) (stagePoint 0 W)) where
  toFun z := {
    toFun t := stageBarycentric F₀ 0 N (z.1, z.2 t)
    continuous_toFun := by fun_prop
    source' := by rw [Path.source]; exact stageBarycentric_point F₀ 0 N z.1
    target' := by rw [Path.target]; exact stageBarycentric_point F₀ 0 N z.1 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z :
      (StdSimplex ℝ (Fin (k + 1)) × Path (stagePoint 0 V) (stagePoint 0 V)) × unitInterval ↦
      stageBarycentric F₀ 0 N (z.1.1, z.1.2 z.2))
    fun_prop

/-- The same common-reference factorization on every original prespectrum level. -/
def prespectrumFamily {k : ℕ} (N : Fin (k + 1) → Node F₀) (n : ℕ) :
    C(StdSimplex ℝ (Fin (k + 1)) × (prespectrum V).space n, (prespectrum W).space n) :=
  Nat.casesOn n (loopFamily F₀ N) (fun r ↦ stageBarycentric F₀ r N)

/-- All native levels retain the original entire simplex family literally. -/
theorem prespectrumFamily_eq {k : ℕ} (N : Fin (k + 1) → Node F₀) (n : ℕ) :
    prespectrumFamily F₀ N n = prespectrumSimplexFamily
      (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)) n := by
  cases n with
  | zero =>
    apply ContinuousMap.ext
    intro z
    change StdSimplex ℝ (Fin (k + 1)) × Path (stagePoint 0 V) (stagePoint 0 V) at z
    apply Path.ext
    funext t
    exact congrArg (fun f ↦ f (z.1, z.2 t)) (stageBarycentric_eq F₀ 0 N)
  | succ r => exact stageBarycentric_eq F₀ r N

/-- The actual original point is retained at every level and every independent parameter. -/
theorem prespectrumFamily_point {k : ℕ} (N : Fin (k + 1) → Node F₀) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1))) :
    prespectrumFamily F₀ N n (z, (prespectrum V).point n) = (prespectrum W).point n := by
  rw [prespectrumFamily_eq]
  exact prespectrumSimplexFamily_point _ n z

/-- The prespectrum structure time remains separate from the entire parameter simplex. -/
theorem prespectrumFamily_structure {k : ℕ} (N : Fin (k + 1) → Node F₀) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) (t : unitInterval) :
    prespectrumFamily F₀ N (n + 1) (z, (prespectrum V).structureMap n x t) =
      (prespectrum W).structureMap n (prespectrumFamily F₀ N n (z, x)) t := by
  rw [prespectrumFamily_eq, prespectrumFamily_eq]
  exact prespectrumSimplexFamily_structure _ n z x t

/-- Level zero keeps the original input-loop coordinate after the exact nerve factorization. -/
theorem prespectrumFamily_zero_apply {k : ℕ} (N : Fin (k + 1) → Node F₀)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : Path (stagePoint 0 V) (stagePoint 0 V))
    (t : unitInterval) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      prespectrumFamily F₀ N 0 (z, x)) t = stageBarycentric F₀ 0 N (z, x t) := rfl

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve
