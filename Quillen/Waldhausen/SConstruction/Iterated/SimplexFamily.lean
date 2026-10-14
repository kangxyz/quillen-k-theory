/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.NerveSimplexFamily
public import Quillen.Waldhausen.SConstruction.Iterated.NaturalTriangle
public import Quillen.Waldhausen.SConstruction.Iterated.TriangleStructure
public import Quillen.Topology.Realization.SimplexCylinder

/-!
# Higher simplex families through every original iterated S-stage

Whole chains of original zero-preserving exact transformations through every iterated S-stage.
This is an intermediate producer; it does not assert compatibility of the raw Bass cube faces.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS

/-- A chain of exact original functors and weak transformations preserving the chosen zero. -/
structure ModelSimplex (V W : Model.{u}) (k : ℕ) where
  /-- The actual natural-transformation chain. -/
  diagram : Fin (k + 1) ⥤ (V ⥤ W)
  exact (i) : IsExact V.waldhausen.cof V.waldhausen.weq
    W.waldhausen.cof W.waldhausen.weq (diagram.obj i)
  zero (i) : (diagram.obj i).obj V.waldhausen.zero = W.waldhausen.zero
  weak (i j) (f : i ⟶ j) (X) : W.waldhausen.weq ((diagram.map f).app X)

namespace ModelSimplex
variable {V W T : Model.{u}} {k : ℕ}

/-- A vertex is precisely an original exact model morphism. -/
def vertex (S : ModelSimplex V W k) (i : Fin (k + 1)) : V ⟶ W :=
  ⟨S.diagram.obj i, S.exact i, S.zero i⟩

/-- The whole transformation chain passes to the actual quotient rows. -/
def rows (S : ModelSimplex V W k) (n : SimplexCategory) :
    ModelSimplex ((IteratedS.rows n).obj V) ((IteratedS.rows n).obj W) k where
  diagram := {
    obj i := ((IteratedS.rows n).map (S.vertex i)).functor
    map {i j} f := rowsTransformation (F := S.vertex i) (G := S.vertex j)
      (S.diagram.map f) n
    map_id i := by
      apply NatTrans.ext
      funext A
      apply ObjectProperty.hom_ext
      ext p
      simp [rowsTransformation]
      rfl
    map_comp f g := by
      apply NatTrans.ext
      funext A
      apply ObjectProperty.hom_ext
      ext p
      simp [rowsTransformation]
      rfl }
  exact i := ((IteratedS.rows n).map (S.vertex i)).exact
  zero i := ((IteratedS.rows n).map (S.vertex i)).zero
  weak i j f := rowsTransformation_weak (F := S.vertex i) (G := S.vertex j)
    (S.diagram.map f) (S.weak i j f) n

/-- Precomposition retains every original transformation. -/
def precomp (S : ModelSimplex V W k) (J : T ⟶ V) : ModelSimplex T W k where
  diagram := S.diagram ⋙ (whiskeringLeft T V W).obj J.functor
  exact i := J.exact.comp (S.exact i)
  zero i := (congrArg (S.diagram.obj i).obj J.zero).trans (S.zero i)
  weak i j f X := S.weak i j f (J.functor.obj X)

/-- Postcomposition retains every original transformation. -/
def postcomp (S : ModelSimplex V W k) (J : W ⟶ T) : ModelSimplex V T k where
  diagram := S.diagram ⋙ (whiskeringRight V W T).obj J.functor
  exact i := (S.exact i).comp J.exact
  zero i := (congrArg J.functor.obj (S.zero i)).trans J.zero
  weak i j f X := J.exact.weak _ (S.weak i j f X)

end ModelSimplex

/-- The same genuine simplex family at each original iterated S-level. -/
def stageSimplexFunction (r : ℕ) :
    {V W : Model.{u}} → {k : ℕ} → ModelSimplex V W k →
    (n : SimplexCategoryᵒᵖ) → ((stages r).obj V).obj n → (Δ[k]).obj n →
      ((stages r).obj W).obj n := by
  induction r with
  | zero =>
    intro V W k S n A τ
    exact (weakNaturalTransformationSimplex V.waldhausen W.waldhausen
      S.diagram S.exact S.weak).app n (A, τ)
  | succ r ih =>
    intro V W k S n A τ
    exact ih (S.rows n.unop) n A τ

/-- Postcomposition retains the whole higher nerve family. -/
theorem nerveSimplexDiagram_postcomp {C D : Type u} [Category C] [Category D]
    {n m : SimplexCategory} {k : ℕ} (K : Fin (k + 1) ⥤ (Grid₂ n m ⥤ C))
    (J : C ⥤ D) (τ : m ⟶ ⦋k⦌) :
    nerveSimplexDiagram (K ⋙ (whiskeringRight _ C D).obj J) τ =
      nerveSimplexDiagram K τ ⋙ J := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp [nerveSimplexDiagram, Functor.uncurry, Functor.map_comp]

/-- The whole iterated simplex is natural under an original exact target functor. -/
theorem stageSimplexFunction_postcomp (r : ℕ) {V W T : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (J : W ⟶ T) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[k]).obj n) :
    stageSimplexFunction r (S.postcomp J) n A τ =
      ((stages r).map J).app n (stageSimplexFunction r S n A τ) := by
  induction r generalizing V W T with
  | zero =>
    apply Subtype.ext
    exact nerveSimplexDiagram_postcomp
      (S.diagram ⋙ (whiskeringLeft _ V W).obj A.val) J.functor τ.down
  | succ r ih =>
    exact ih (S.rows n.unop) ((IteratedS.rows n.unop).map J) A

/-- The whole iterated simplex is natural under an original exact source functor. -/
theorem stageSimplexFunction_precomp (r : ℕ) {V W T : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (J : T ⟶ V) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj T).obj n) (τ : (Δ[k]).obj n) :
    stageSimplexFunction r (S.precomp J) n A τ =
      stageSimplexFunction r S n (((stages r).map J).app n A) τ := by
  induction r generalizing V W T with
  | zero => rfl
  | succ r ih =>
    exact ih (S.rows n.unop) ((IteratedS.rows n.unop).map J) A

/-- Simplicial reindexing retains the full original higher transformation family. -/
theorem stageSimplexFunction_naturality (r : ℕ) {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (A : ((stages r).obj V).obj n) (τ : (Δ[k]).obj n) :
    ((stages r).obj W).map α (stageSimplexFunction r S n A τ) =
      stageSimplexFunction r S m (((stages r).obj V).map α A) ((Δ[k]).map α τ) := by
  induction r generalizing V W with
  | zero => rfl
  | succ r ih =>
    change ((stages r).obj ((rows m.unop).obj W)).map α
      (((stages r).map ((rowsReindex α.unop).app W)).app n
        (stageSimplexFunction r (S.rows n.unop) n A τ)) = _
    rw [← stageSimplexFunction_postcomp, ih]
    change stageSimplexFunction r ((S.rows m.unop).precomp ((rowsReindex α.unop).app V))
      m (((stages r).obj ((rows n.unop).obj V)).map α A) ((Δ[k]).map α τ) = _
    rw [stageSimplexFunction_precomp]
    congr 1
    exact ConcreteCategory.congr_hom
      (((stages r).map ((rowsReindex α.unop).app V)).naturality α) A

/-- The actual simplicial higher family at each original iterated stage. -/
def stageTransformationSimplex (r : ℕ) {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) : (stages r).obj V ⊗ Δ[k] ⟶ (stages r).obj W where
  app n := ↾fun z ↦ stageSimplexFunction r S n z.1 z.2
  naturality n m α := by
    ext z : 3
    exact (stageSimplexFunction_naturality r S α z.1 z.2).symm

namespace ModelSimplex
/-- Proof fields add no extra coherence to a fixed original chain. -/
theorem ext_diagram {V W : Model.{u}} {k : ℕ} {S T : ModelSimplex V W k}
    (h : S.diagram = T.diagram) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- All transformation components obey the original row-insertion square at once. -/
theorem insertion_square {V W : Model.{u}} {k : ℕ} (S : ModelSimplex V W k)
    {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    S.postcomp ((insertion τ).app W) = (S.rows n).precomp ((insertion τ).app V) := by
  apply ext_diagram
  refine CategoryTheory.Functor.ext
    (fun i ↦ congrArg Model.Hom.functor ((insertion τ).naturality (S.vertex i))) ?_
  intro i j f
  have h := rowsTransformation_insertion_square (F := S.vertex i) (G := S.vertex j)
    (S.diagram.map f) τ
  apply (cancel_mono (eqToHom
    (congrArg Model.Hom.functor ((insertion τ).naturality (S.vertex j))))).1
  simpa only [postcomp, precomp, rows, vertex, Functor.comp_obj, Functor.comp_map,
    whiskeringLeft_obj_obj, whiskeringRight_obj_obj,
    whiskeringLeft_obj_map, whiskeringRight_obj_map,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h
end ModelSimplex

/-- Every higher simplex retains a separate original suspension coordinate. -/
theorem stageSimplexFunction_structure (r : ℕ) {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) (theta : (Δ[k]).obj n) :
    stageSimplexFunction (r + 1) S n ((stageCylinder r V).app n (A, τ)) theta =
      (stageCylinder r W).app n (stageSimplexFunction r S n A theta, τ) := by
  change stageSimplexFunction r (S.rows n.unop) n
    (((stages r).map ((insertion τ.down).app V)).app n A) theta = _
  rw [← stageSimplexFunction_precomp, ← ModelSimplex.insertion_square]
  exact stageSimplexFunction_postcomp r S ((insertion τ.down).app W) n A theta

/-- The complete mixed-coordinate simplicial square preserves the higher original simplex. -/
theorem stageTransformationSimplex_structure (r : ℕ) {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) :
    stageCylinder r V ▷ Δ[k] ≫ stageTransformationSimplex (r + 1) S =
      simplicialSimplexCylinderSwap ((stages r).obj V) k ≫
        stageTransformationSimplex r S ▷ Δ[1] ≫ stageCylinder r W := by
  ext n z : 4
  exact stageSimplexFunction_structure r S n z.1.1 z.1.2 z.2

/-- The genuine continuous higher family at each original stage. -/
def stageSimplexRealization (r : ℕ) {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) : C(stageSpace r V × |(Δ[k] : SSet.{u})|, stageSpace r W) :=
  realizationSimplexFamily (stageTransformationSimplex r S)

/-- The realized higher simplex keeps its whole parameter independent from structure time. -/
theorem stageSimplexRealization_structure (r : ℕ) {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (z : |(Δ[k] : SSet.{u})|) (t : unitInterval)
    (x : stageSpace r V) :
    stageSimplexRealization (r + 1) S (stageLoopMap r V x t, z) =
      stageLoopMap r W (stageSimplexRealization r S (x, z)) t :=
  realizationSimplexFamily_interchange (stageTransformationSimplex r S)
    (stageTransformationSimplex (r + 1) S) (stageHomotopy r V) (stageHomotopy r W)
    (stageTransformationSimplex_structure r S) z t x

namespace ModelSimplex
/-- The actual subchain selected by any simplex face or degeneracy. -/
def face {V W : Model.{u}} {k l : ℕ} (S : ModelSimplex V W k)
    (α : ⦋l⦌ ⟶ ⦋k⦌) : ModelSimplex V W l where
  diagram := α.toOrderHom.monotone.functor ⋙ S.diagram
  exact i := S.exact (α.toOrderHom i)
  zero i := S.zero (α.toOrderHom i)
  weak _i _j f X := S.weak _ _ (α.toOrderHom.monotone.functor.map f) X
end ModelSimplex

/-- Every iterated simplex face is the full original iterated family of its subchain. -/
theorem stageSimplexFunction_face (r : ℕ) {V W : Model.{u}} {k l : ℕ}
    (S : ModelSimplex V W k) (α : ⦋l⦌ ⟶ ⦋k⦌) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[l]).obj n) :
    stageSimplexFunction r S n A ⟨τ.down ≫ α⟩ =
      stageSimplexFunction r (S.face α) n A τ := by
  induction r generalizing V W with
  | zero => rfl
  | succ r ih => exact ih (S.rows n.unop) A

/-- The simplicial face equations retain every point of the original subchain family. -/
theorem stageTransformationSimplex_face (r : ℕ) {V W : Model.{u}} {k l : ℕ}
    (S : ModelSimplex V W k) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    ((𝟙 ((stages r).obj V)) ⊗ₘ SSet.stdSimplex.map α) ≫ stageTransformationSimplex r S =
      stageTransformationSimplex r (S.face α) := by
  ext n z : 4
  exact stageSimplexFunction_face r S α n z.1 z.2

/-- Every original zero simplex is fixed throughout the higher family. -/
theorem stageSimplexFunction_zeroSimplex (r : ℕ) {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (n : SimplexCategoryᵒᵖ) (τ : (Δ[k]).obj n) :
    stageSimplexFunction r S n (stageZeroSimplex r V n) τ = stageZeroSimplex r W n := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    exact nerveSimplexDiagram_eq_const_of_zero _ W.waldhausen.zero W.waldhausen.isZero
      (fun i _ ↦ S.zero i) τ.down
  | succ r ih =>
    rw [stageZeroSimplex_succ, stageZeroSimplex_succ]
    exact ih (S.rows n.unop)

/-- The complete original higher simplex is constant along the original chosen-zero vertex. -/
theorem stageTransformationSimplex_fixed_vertex (r : ℕ) {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) :
    SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[k] ≫ stageTransformationSimplex r S =
      CartesianMonoidalCategory.fst Δ[0] Δ[k] ≫ SSet.yonedaEquiv.symm (stageVertex r W) := by
  ext n z : 4
  change stageSimplexFunction r S n
    (((stages r).obj V).map z.1.down.op (stageVertex r V)) z.2 =
      ((stages r).obj W).map z.1.down.op (stageVertex r W)
  have hz : z.1.down = n.unop.const ⦋0⦌ 0 :=
    @Subsingleton.elim (n.unop ⟶ ⦋0⦌) inferInstance _ _
  rw [hz]
  exact stageSimplexFunction_zeroSimplex r S n z.2

/-- The realized higher family fixes the actual original stage point throughout. -/
theorem stageSimplexRealization_fixed_point (r : ℕ) {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (z : |(Δ[k] : SSet.{u})|) :
    stageSimplexRealization r S (stagePoint r V, z) = stagePoint r W := by
  let p := (realizationProductSimplexIso (Δ[0] : SSet.{u}) k).inv (default, z)
  have hn := ConcreteCategory.congr_hom
    (realizationProductSimplexIso_inv_whisker (SSet.yonedaEquiv.symm (stageVertex r V)) k)
    (default, z)
  change SSet.toTop.map (SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[k]) p =
    (realizationProductSimplexIso ((stages r).obj V) k).inv (stagePoint r V, z) at hn
  change SSet.toTop.map (stageTransformationSimplex r S)
    ((realizationProductSimplexIso ((stages r).obj V) k).inv (stagePoint r V, z)) = _
  rw [← hn]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[k]) ≫
    SSet.toTop.map (stageTransformationSimplex r S)) p = _
  rw [← Functor.map_comp, stageTransformationSimplex_fixed_vertex,
    Functor.map_comp, TopCat.comp_app]
  rw [Subsingleton.elim (SSet.toTop.map (CartesianMonoidalCategory.fst Δ[0] Δ[k]) p) default]
  rfl

end Quillen.Waldhausen.IteratedS
