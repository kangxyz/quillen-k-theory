import Quillen.CategoryTheory.TheoremB.RealizedRowFibers
import Quillen.CategoryTheory.TheoremB.ReplacementSplitting

/-!
# Genuine homotopy pullback squares in the comma replacement

This module uses the compact-open path-space model of a homotopy pullback.
For a discrete left-hand base it identifies this space homeomorphically with
the coproduct of the actual homotopy fibers. Consequently Theorem B's
transition hypothesis makes every complete replacement-row square homotopy
cartesian, with the canonical constant-path comparison as forward map.
This remains a row theorem, not a claim about the total realization.
-/

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen

/-- The actual path-space homotopy pullback of `f` along `g`. Its topology is
inherited from the product with the compact-open path space. -/
def HomotopyPullback {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A]
    [TopologicalSpace B] (f : C(X, B)) (g : C(A, B)) :=
  {z : A × (X × C(I, B)) // z.2.2 0 = f z.2.1 ∧ z.2.2 1 = g z.1}

namespace HomotopyPullback

variable {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A]
  [TopologicalSpace B] (f : C(X, B)) (g : C(A, B))

instance : TopologicalSpace (HomotopyPullback f g) := inferInstanceAs
  (TopologicalSpace {z : A × (X × C(I, B)) // z.2.2 0 = f z.2.1 ∧ z.2.2 1 = g z.1})

/-- Projection to the space along which the homotopy pullback was taken. -/
def baseProjection : C(HomotopyPullback f g, A) where
  toFun z := z.1.1
  continuous_toFun := by fun_prop

/-- Projection to the original source. -/
def sourceProjection : C(HomotopyPullback f g, X) where
  toFun z := z.1.2.1
  continuous_toFun := by fun_prop

/-- A strictly commuting square has its canonical constant-path comparison. -/
def comparison {W : Type u} [TopologicalSpace W] (a : C(W, A)) (h : C(W, X))
    (comm : f.comp h = g.comp a) : C(W, HomotopyPullback f g) where
  toFun w := ⟨(a w, h w, ContinuousMap.const I (g (a w))),
    (ContinuousMap.congr_fun comm w).symm, rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact a.continuous.prodMk (h.continuous.prodMk (by fun_prop))

@[simp]
theorem comparison_baseProjection {W : Type u} [TopologicalSpace W]
    (a : C(W, A)) (h : C(W, X)) (comm : f.comp h = g.comp a) :
    (baseProjection f g).comp (comparison f g a h comm) = a := rfl

@[simp]
theorem comparison_sourceProjection {W : Type u} [TopologicalSpace W]
    (a : C(W, A)) (h : C(W, X)) (comm : f.comp h = g.comp a) :
    (sourceProjection f g).comp (comparison f g a h comm) = h := rfl

/-- The coproduct of point fibers maps into the actual homotopy pullback. -/
def sigmaFibersMap : C((Σ a : A, HomotopyFiber f (g a)), HomotopyPullback f g) where
  toFun z := ⟨(z.1, z.2.1), z.2.2⟩
  continuous_toFun := continuous_sigma fun _a ↦
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- Over a discrete parameter space, the coproduct-of-fibers topology is
exactly the topology of the genuine homotopy pullback. -/
def sigmaFibersHomeomorph [DiscreteTopology A] :
    (Σ a : A, HomotopyFiber f (g a)) ≃ₜ HomotopyPullback f g := by
  have hind : Topology.IsInducing (sigmaFibersMap f g) := by
    apply inducing_sigma.mpr
    constructor
    · intro a
      exact ((isInducing_prodMkRight (Y := X × C(I, B)) a).comp
        (show Topology.IsInducing (Subtype.val : HomotopyFiber f (g a) → X × C(I, B))
          from Topology.IsInducing.subtypeVal)).codRestrict
        (s := ({z | z.2.2 0 = f z.2.1 ∧ z.2.2 1 = g z.1} : Set (A × (X × C(I, B)))))
        (fun z ↦ z.2)
    · intro a
      refine ⟨(baseProjection f g) ⁻¹' {a},
        (isOpen_discrete {a}).preimage (baseProjection f g).continuous, ?_⟩
      intro z
      rfl
  have hinj : Function.Injective (sigmaFibersMap f g) := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hab : a = b := congrArg (fun z : HomotopyPullback f g ↦ z.1.1) h
    subst b
    have hxy : x = y := Subtype.ext (congrArg (fun z : HomotopyPullback f g ↦ z.1.2) h)
    subst y
    rfl
  apply (Topology.IsEmbedding.mk hind hinj).toHomeomorphOfSurjective
  intro z
  exact ⟨⟨z.1.1, ⟨z.1.2, z.2⟩⟩, rfl⟩

@[simp]
theorem sigmaFibersHomeomorph_apply [DiscreteTopology A]
    (z : Σ a : A, HomotopyFiber f (g a)) :
    sigmaFibersHomeomorph f g z = sigmaFibersMap f g z := rfl

/-- A homeomorphism in the source induces a homeomorphism of actual
homotopy pullbacks, leaving the base point and target path unchanged. -/
def sourceHomeomorph {Y : Type u} [TopologicalSpace Y] (e : Y ≃ₜ X) :
    HomotopyPullback (f.comp (e : C(Y, X))) g ≃ₜ HomotopyPullback f g where
  toFun z := ⟨(z.1.1, e z.1.2.1, z.1.2.2), z.2⟩
  invFun z := ⟨(z.1.1, e.symm z.1.2.1, z.1.2.2), by simpa using z.2⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (by fun_prop : Continuous fun z : HomotopyPullback (f.comp (e : C(Y, X))) g ↦
      (z.1.1, e z.1.2.1, z.1.2.2))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (by fun_prop : Continuous fun z : HomotopyPullback f g ↦
      (z.1.1, e.symm z.1.2.1, z.1.2.2))

end HomotopyPullback

namespace TheoremB

section CoproductSquares

variable {ι κ : Type u} [TopologicalSpace ι] [DiscreteTopology ι]
  [TopologicalSpace κ] [DiscreteTopology κ]
  {X : ι → Type u} {Y : κ → Type u}
  [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]

/-- The base map of a reindexed coproduct square. -/
def discreteReindexMap (a : ι → κ) : C(ι, κ) := ⟨a, continuous_of_discreteTopology⟩

/-- The canonical comparison of a reindexed coproduct square to its actual
homotopy pullback. -/
def sigmaSquareComparison (a : ι → κ) (f : ∀ i, C(X i, Y (a i))) :
    C((Σ i, X i), HomotopyPullback (sigmaProjection Y) (discreteReindexMap a)) :=
  HomotopyPullback.comparison _ _ (sigmaProjection X)
    (sigmaReindexContinuousMap a f) rfl

/-- The path-space pullback of a coproduct projection along a discrete map
is homeomorphic to the coproduct of the selected fibers. -/
def sigmaPullbackHomeomorph (a : ι → κ) :
    (Σ i, Y (a i)) ≃ₜ HomotopyPullback (sigmaProjection Y) (discreteReindexMap a) := by
  let E : (Σ i, Y (a i)) ≃ₜ Σ i, HomotopyFiber (sigmaProjection Y) (a i) :=
    { toFun z := ⟨z.1, (sigmaProjectionFiberHomeomorph Y (a z.1)).symm z.2⟩
      invFun z := ⟨z.1, sigmaProjectionFiberHomeomorph Y (a z.1) z.2⟩
      left_inv z := by cases z; simp
      right_inv z := by cases z; simp
      continuous_toFun := continuous_sigma fun i ↦ continuous_sigmaMk.comp
        (sigmaProjectionFiberHomeomorph Y (a i)).symm.continuous
      continuous_invFun := continuous_sigma fun i ↦ continuous_sigmaMk.comp
        (sigmaProjectionFiberHomeomorph Y (a i)).continuous }
  exact E.trans (HomotopyPullback.sigmaFibersHomeomorph (sigmaProjection Y)
    (discreteReindexMap a))

/-- Componentwise homotopy equivalences make the entire coproduct square
homotopy cartesian. No equivalence of the index spaces is required. -/
def sigmaSquareHomotopyEquiv (a : ι → κ)
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y (a i))) :
    ContinuousMap.HomotopyEquiv (Σ i, X i)
      (HomotopyPullback (sigmaProjection Y) (discreteReindexMap a)) :=
  (TheoremA.sigmaHomotopyEquiv e).trans (sigmaPullbackHomeomorph a).toHomotopyEquiv

/-- The homotopy equivalence uses exactly the canonical comparison map. -/
@[simp]
theorem sigmaSquareHomotopyEquiv_toFun (a : ι → κ)
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y (a i))) :
    (sigmaSquareHomotopyEquiv a e).toFun = sigmaSquareComparison a (fun i ↦ (e i).toFun) := rfl

end CoproductSquares

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The complete topological comma-replacement square, compared with the
actual homotopy pullback of its lower and right-hand maps. -/
def commaRowSquareComparison {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    C((topologicalReplacement (TheoremA.commaNerveDiagram F)).obj p,
      HomotopyPullback (commaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α))) :=
  sigmaSquareComparison (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α)
    (fun s ↦ transitionMap F (TheoremA.firstVertexEdge α s))

/-- Theorem B's precise hypothesis makes every topological replacement
square genuinely homotopy cartesian. -/
def commaRowSquareHomotopyEquiv (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    ContinuousMap.HomotopyEquiv
      ((topologicalReplacement (TheoremA.commaNerveDiagram F)).obj p)
      (HomotopyPullback (commaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α))) :=
  sigmaSquareHomotopyEquiv (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α)
    (fun s ↦ transitionHomotopyEquiv F h (TheoremA.firstVertexEdge α s))

@[simp]
theorem commaRowSquareHomotopyEquiv_toFun (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    (commaRowSquareHomotopyEquiv F h α).toFun = commaRowSquareComparison F α := rfl

/-- The actual realized row square has its canonical constant-path map
into the actual path-space homotopy pullback. -/
def realizedCommaRowSquareComparison {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    C(|TheoremA.replacementRow (TheoremA.commaNerveDiagram F) p|,
      HomotopyPullback (realizedCommaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α))) :=
  HomotopyPullback.comparison _ _ (realizedCommaRowProjection F p)
    (SSet.toTop.map (TheoremA.replacementRowMap (TheoremA.commaNerveDiagram F) α)).hom
    (ContinuousMap.ext fun x ↦ (realizedCommaRowProjection_naturality F α x).symm)

/-- Row coordinates transport the entire homotopy pullback, including its
path-space topology. -/
def realizedCommaRowPullbackCoordinates {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    HomotopyPullback (realizedCommaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α)) ≃ₜ
      HomotopyPullback (commaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α)) :=
  HomotopyPullback.sourceHomeomorph (commaRowProjection F q) _
    (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso (TheoremA.commaNerveDiagram F) q))

/-- The actual row comparison becomes the coproduct comparison under the
proved coordinate homeomorphisms. -/
theorem realizedCommaRowSquareComparison_coordinates {p q : SimplexCategoryᵒᵖ}
    (α : p ⟶ q) (x : |TheoremA.replacementRow (TheoremA.commaNerveDiagram F) p|) :
    realizedCommaRowPullbackCoordinates F α (realizedCommaRowSquareComparison F α x) =
      commaRowSquareComparison F α
        ((TheoremA.replacementRowRealizationIso (TheoremA.commaNerveDiagram F) p).hom x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact ConcreteCategory.congr_hom
        (replacementRowRealizationIso_naturality (TheoremA.commaNerveDiagram F) α) x
    · rfl

/-- Under precisely Theorem B's transition hypothesis, each complete
square of the actual realized rows is homotopy cartesian. -/
def realizedCommaRowSquareHomotopyEquiv (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    ContinuousMap.HomotopyEquiv
      |TheoremA.replacementRow (TheoremA.commaNerveDiagram F) p|
      (HomotopyPullback (realizedCommaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α))) :=
  ((TopCat.homeoOfIso
    (TheoremA.replacementRowRealizationIso (TheoremA.commaNerveDiagram F) p)).toHomotopyEquiv.trans
      (commaRowSquareHomotopyEquiv F h α)).trans
        (realizedCommaRowPullbackCoordinates F α).symm.toHomotopyEquiv

/-- The cartesian equivalence retains the canonical actual-row comparison
as its forward continuous map. -/
@[simp]
theorem realizedCommaRowSquareHomotopyEquiv_toFun (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    (realizedCommaRowSquareHomotopyEquiv F h α).toFun =
      realizedCommaRowSquareComparison F α := by
  apply ContinuousMap.ext
  intro x
  apply (realizedCommaRowPullbackCoordinates F α).injective
  change realizedCommaRowPullbackCoordinates F α
    ((realizedCommaRowPullbackCoordinates F α).symm _) = _
  rw [Homeomorph.apply_symm_apply, realizedCommaRowSquareComparison_coordinates]
  rfl

end TheoremB
end Quillen
