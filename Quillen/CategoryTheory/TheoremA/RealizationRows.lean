/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.HomotopyBridge
public import Quillen.CategoryTheory.TheoremA.SimplicialReplacement
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Realization of the rows of a simplicial replacement

The coproduct of a family of simplicial sets realizes to the topological
disjoint union of their realizations. In particular, a family of actual
homotopy equivalences gives an actual homotopy equivalence on each row of
the simplicial replacement. The forward map is the canonical induced map.

This is the rowwise step only. Passing from rowwise homotopy equivalences
to the realization of a bisimplicial set requires a separate gluing theorem.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TheoremA

variable {ι : Type u}

/-- The degreewise disjoint union of a family of simplicial sets. -/
def simplicialSigma (X : ι → SSet.{u}) : SSet.{u} where
  obj n := Σ i, (X i).obj n
  map f := ↾fun x ↦ ⟨x.1, (X x.1).map f x.2⟩
  map_id n := by ext x : 3; dsimp; simp
  map_comp f g := by ext x : 3; dsimp; simp

/-- The inclusion of one summand. -/
def simplicialSigmaι (X : ι → SSet.{u}) (i : ι) : X i ⟶ simplicialSigma X where
  app _n := ↾fun x ↦ ⟨i, x⟩
  naturality _ _ _ := rfl

/-- Maps of the summands induce the canonical map on their disjoint union. -/
def simplicialSigmaMap {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i) :
    simplicialSigma X ⟶ simplicialSigma Y where
  app n := ↾fun x ↦ ⟨x.1, (f x.1).app n x.2⟩
  naturality n m α := by
    ext ⟨i, x⟩ : 3
    exact congrArg (Sigma.mk i) (ConcreteCategory.congr_hom ((f i).naturality α) x)

@[reassoc (attr := simp)]
theorem simplicialSigmaι_map {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i) (i : ι) :
    simplicialSigmaι X i ≫ simplicialSigmaMap f = f i ≫ simplicialSigmaι Y i := rfl

/-- The explicit disjoint union is the categorical coproduct. -/
def simplicialSigmaIsColimit (X : ι → SSet.{u}) :
    IsColimit (Cofan.mk (simplicialSigma X) (simplicialSigmaι X)) :=
  Cofan.IsColimit.mk _
    (fun s ↦ {
      app := fun n ↦ ↾fun x ↦ (s.inj x.1).app n x.2
      naturality := by
        intro n m α
        ext ⟨i, x⟩ : 3
        exact ConcreteCategory.congr_hom ((s.inj i).naturality α) x })
    (by intro s i; rfl)
    (by
      intro s m h
      ext n ⟨i, x⟩ : 4
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (h i) n) x)

/-- Realization preserves the explicit coproduct cocone. -/
def realizedSigmaIsColimit (X : ι → SSet.{u}) :
    IsColimit (Cofan.mk (SSet.toTop.obj (simplicialSigma X))
      (fun i ↦ SSet.toTop.map (simplicialSigmaι X i))) :=
  isColimitCofanMkObjOfIsColimit SSet.toTop X (simplicialSigmaι X)
    (simplicialSigmaIsColimit X)

/-- Realization of a simplicial coproduct is the actual topological disjoint union. -/
def realizationSigmaIso (X : ι → SSet.{u}) :
    SSet.toTop.obj (simplicialSigma X) ≅ TopCat.of (Σ i, |X i|) :=
  (realizedSigmaIsColimit X).coconePointUniqueUpToIso
    (TopCat.sigmaCofanIsColimit fun i ↦ SSet.toTop.obj (X i))

@[reassoc (attr := simp)]
theorem realizationSigmaIso_ι (X : ι → SSet.{u}) (i : ι) :
    SSet.toTop.map (simplicialSigmaι X i) ≫ (realizationSigmaIso X).hom =
      TopCat.sigmaι (fun i ↦ SSet.toTop.obj (X i)) i := by
  exact (realizedSigmaIsColimit X).comp_coconePointUniqueUpToIso_hom _ ⟨i⟩

@[simp]
theorem realizationSigmaIso_ι_apply (X : ι → SSet.{u}) (i : ι) (x : |X i|) :
    (realizationSigmaIso X).hom (SSet.toTop.map (simplicialSigmaι X i) x) = ⟨i, x⟩ :=
  ConcreteCategory.congr_hom (realizationSigmaIso_ι X i) x

@[simp]
theorem realizationSigmaIso_inv_apply (X : ι → SSet.{u}) (i : ι) (x : |X i|) :
    (realizationSigmaIso X).inv ⟨i, x⟩ = SSet.toTop.map (simplicialSigmaι X i) x := by
  rw [← realizationSigmaIso_ι_apply X i x]
  exact ConcreteCategory.congr_hom (realizationSigmaIso X).hom_inv_id _

/-- A family of continuous maps acts continuously on the topological disjoint union. -/
def sigmaContinuousMap {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, C(X i, Y i)) : C((Σ i, X i), Σ i, Y i) :=
  ContinuousMap.sigma fun i ↦ (ContinuousMap.sigmaMk i).comp (f i)

/-- A family of homotopies acts continuously on the topological disjoint union. -/
def sigmaHomotopy {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f g : ∀ i, C(X i, Y i)}
    (h : ∀ i, (f i).Homotopy (g i)) :
    (sigmaContinuousMap f).Homotopy (sigmaContinuousMap g) where
  toFun z := ⟨z.2.1, h z.2.1 (z.1, z.2.2)⟩
  continuous_toFun := by
    let e : (unitInterval × Σ i, X i) ≃ₜ Σ i, X i × unitInterval :=
      (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib
    have hc : Continuous (fun z : (Σ i, X i × unitInterval) ↦
        (⟨z.1, h z.1 (z.2.2, z.2.1)⟩ : Σ i, Y i)) :=
      continuous_sigma fun i ↦ continuous_sigmaMk.comp
        ((h i).continuous.comp (continuous_snd.prodMk continuous_fst))
    exact hc.comp e.continuous
  map_zero_left x := by cases x; simp [sigmaContinuousMap]
  map_one_left x := by cases x; simp [sigmaContinuousMap]

/-- Homotopy equivalences assemble over a disjoint union, without any coherence
conditions between distinct components. -/
def sigmaHomotopyEquiv {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    ContinuousMap.HomotopyEquiv (Σ i, X i) (Σ i, Y i) where
  toFun := sigmaContinuousMap fun i ↦ (e i).toFun
  invFun := sigmaContinuousMap fun i ↦ (e i).invFun
  left_inv := ⟨sigmaHomotopy fun i ↦ (e i).left_inv.some⟩
  right_inv := ⟨sigmaHomotopy fun i ↦ (e i).right_inv.some⟩

/-- The disjoint-union homeomorphism intertwines the canonical realized map
with the actual disjoint union of the realized component maps. -/
theorem realizationSigmaIso_naturality {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i) :
    SSet.toTop.map (simplicialSigmaMap f) ≫ (realizationSigmaIso Y).hom =
      (realizationSigmaIso X).hom ≫
        TopCat.ofHom (sigmaContinuousMap fun i ↦ (SSet.toTop.map (f i)).hom) := by
  apply (realizedSigmaIsColimit X).hom_ext
  intro ⟨i⟩
  dsimp
  rw [← Category.assoc, ← Functor.map_comp, simplicialSigmaι_map, Functor.map_comp,
    Category.assoc, realizationSigmaIso_ι, ← Category.assoc, realizationSigmaIso_ι]
  rfl

/-- A family of genuine homotopy equivalences of realizations induces a genuine
homotopy equivalence on the realized simplicial coproduct. -/
def realizationSigmaHomotopyEquiv {X Y : ι → SSet.{u}}
    (e : ∀ i, ContinuousMap.HomotopyEquiv |X i| |Y i|) :
    ContinuousMap.HomotopyEquiv |simplicialSigma X| |simplicialSigma Y| :=
  ((TopCat.homeoOfIso (realizationSigmaIso X)).toHomotopyEquiv.trans
    (sigmaHomotopyEquiv e)).trans
      (TopCat.homeoOfIso (realizationSigmaIso Y).symm).toHomotopyEquiv

/-- If the fiber equivalences have the specified canonical forward maps, so
does the resulting equivalence on the realized coproduct. -/
theorem realizationSigmaHomotopyEquiv_toFun {X Y : ι → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i)
    (e : ∀ i, ContinuousMap.HomotopyEquiv |X i| |Y i|)
    (he : ∀ i, (e i).toFun = (SSet.toTop.map (f i)).hom) :
    (realizationSigmaHomotopyEquiv e).toFun =
      (SSet.toTop.map (simplicialSigmaMap f)).hom := by
  apply ContinuousMap.ext
  intro x
  have h := ConcreteCategory.congr_hom (realizationSigmaIso_naturality f) x
  change (realizationSigmaIso Y).inv
      ⟨((realizationSigmaIso X).hom x).1,
        (e ((realizationSigmaIso X).hom x).1).toFun ((realizationSigmaIso X).hom x).2⟩ = _
  rw [he]
  change (realizationSigmaIso Y).inv
      ((TopCat.ofHom (sigmaContinuousMap fun i ↦ (SSet.toTop.map (f i)).hom))
        ((realizationSigmaIso X).hom x)) = _
  change (realizationSigmaIso Y).hom
      (SSet.toTop.map (simplicialSigmaMap f) x) =
    (TopCat.ofHom (sigmaContinuousMap fun i ↦ (SSet.toTop.map (f i)).hom))
      ((realizationSigmaIso X).hom x) at h
  rw [← h]
  exact ConcreteCategory.congr_hom (realizationSigmaIso Y).hom_inv_id _

/-- The realization of a replacement row is the disjoint union of the
realizations of its fibers over all base chains. -/
def replacementRowRealizationIso {D : Type u} [SmallCategory D]
    (H : D ⥤ SSet.{u}) (p : SimplexCategoryᵒᵖ) :
    |replacementRow H p| ≅ TopCat.of (Σ s : (nerve D).obj p, |H.obj (s.obj 0)|) :=
  realizationSigmaIso fun s : (nerve D).obj p ↦ H.obj (s.obj 0)

/-- Objectwise homotopy equivalences give actual homotopy equivalences on
all realized replacement rows. No natural choice of inverse is required. -/
def replacementRowRealizationHomotopyEquiv {D : Type u} [SmallCategory D]
    {H K : D ⥤ SSet.{u}}
    (e : ∀ d, ContinuousMap.HomotopyEquiv |H.obj d| |K.obj d|)
    (p : SimplexCategoryᵒᵖ) :
    ContinuousMap.HomotopyEquiv |replacementRow H p| |replacementRow K p| :=
  realizationSigmaHomotopyEquiv fun s : (nerve D).obj p ↦ e (s.obj 0)

/-- For a natural transformation whose component realizations are homotopy
 equivalences, the canonical row map is the forward map of the row equivalence. -/
theorem replacementRowRealizationHomotopyEquiv_toFun
    {D : Type u} [SmallCategory D] {H K : D ⥤ SSet.{u}} (η : H ⟶ K)
    (e : ∀ d, ContinuousMap.HomotopyEquiv |H.obj d| |K.obj d|)
    (he : ∀ d, (e d).toFun = (SSet.toTop.map (η.app d)).hom)
    (p : SimplexCategoryᵒᵖ) :
    (replacementRowRealizationHomotopyEquiv e p).toFun =
      (SSet.toTop.map (replacementRowNatMap η p)).hom :=
  realizationSigmaHomotopyEquiv_toFun
    (fun s : (nerve D).obj p ↦ η.app (s.obj 0))
    (fun s : (nerve D).obj p ↦ e (s.obj 0))
    (fun s : (nerve D).obj p ↦ he (s.obj 0))

/-- The inclusion of a summand remains a closed embedding after realization. -/
theorem realizationSigmaι_isClosedEmbedding (X : ι → SSet.{u}) (i : ι) :
    Topology.IsClosedEmbedding (SSet.toTop.map (simplicialSigmaι X i)) := by
  have h := (TopCat.homeoOfIso (realizationSigmaIso X).symm).isClosedEmbedding.comp
    (Topology.IsClosedEmbedding.sigmaMk («σ» := fun i ↦ |X i|) (i := i))
  change Topology.IsClosedEmbedding
    (fun x : |X i| ↦ (realizationSigmaIso X).inv ⟨i, x⟩) at h
  have heq : (fun x : |X i| ↦ (realizationSigmaIso X).inv ⟨i, x⟩) =
      (fun x : |X i| ↦ SSet.toTop.map (simplicialSigmaι X i) x) :=
    funext (realizationSigmaIso_inv_apply X i)
  rw [heq] at h
  exact h

/-- The inclusion of a summand also remains an open embedding after realization. -/
theorem realizationSigmaι_isOpenEmbedding (X : ι → SSet.{u}) (i : ι) :
    Topology.IsOpenEmbedding (SSet.toTop.map (simplicialSigmaι X i)) := by
  have h := (TopCat.homeoOfIso (realizationSigmaIso X).symm).isOpenEmbedding.comp
    (Topology.IsOpenEmbedding.sigmaMk («σ» := fun i ↦ |X i|) (i := i))
  change Topology.IsOpenEmbedding
    (fun x : |X i| ↦ (realizationSigmaIso X).inv ⟨i, x⟩) at h
  have heq : (fun x : |X i| ↦ (realizationSigmaIso X).inv ⟨i, x⟩) =
      (fun x : |X i| ↦ SSet.toTop.map (simplicialSigmaι X i) x) :=
    funext (realizationSigmaIso_inv_apply X i)
  rw [heq] at h
  exact h

/-- The unique diagram map to the point simplicial set. -/
def replacementPointAugmentation {D : Type u} [SmallCategory D]
    (H : D ⥤ SSet.{u}) : H ⟶ (Functor.const D).obj (Δ[0] : SSet.{u}) where
  app d := SSet.stdSimplex.isTerminalObj₀.from (H.obj d)
  naturality _ _ _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Contractible fibers give actual homotopy equivalences on the realized
rows of the canonical augmentation to the constant point diagram. -/
def contractibleReplacementRowHomotopyEquiv {D : Type u} [SmallCategory D]
    (H : D ⥤ SSet.{u}) (h : ∀ d, ContractibleSpace |H.obj d|)
    (p : SimplexCategoryᵒᵖ) :
    ContinuousMap.HomotopyEquiv |replacementRow H p|
      |replacementRow ((Functor.const D).obj (Δ[0] : SSet.{u})) p| :=
  replacementRowRealizationHomotopyEquiv (fun d ↦ by
    letI := h d
    exact (ContractibleSpace.hequiv |H.obj d| |(Δ[0] : SSet.{u})|).some) p

/-- The contractible-row equivalence realizes the canonical augmentation,
not an unspecified equivalence of the same two spaces. -/
theorem contractibleReplacementRowHomotopyEquiv_toFun
    {D : Type u} [SmallCategory D]
    (H : D ⥤ SSet.{u}) (h : ∀ d, ContractibleSpace |H.obj d|)
    (p : SimplexCategoryᵒᵖ) :
    (contractibleReplacementRowHomotopyEquiv H h p).toFun =
      (SSet.toTop.map (replacementRowNatMap (replacementPointAugmentation H) p)).hom := by
  apply replacementRowRealizationHomotopyEquiv_toFun
  intro d
  apply ContinuousMap.ext
  intro x
  exact @Subsingleton.elim |(Δ[0] : SSet.{u})| inferInstance _ _

end Quillen.TheoremA
