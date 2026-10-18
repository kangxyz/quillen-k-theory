/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.LocalCoefficients.Homology
public import Quillen.Topology.LocalCoefficients.IntegralChainEvaluation
public import Quillen.Topology.LocalCoefficients.Prism
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Quillen.Aglib.RepresentationTheory.Homological.GroupHomology.IntegralBar

/-!
# The original singular-to-integral-bar map in degree two

The original chains, signs, maps, basepoints and stated hypotheses are retained.
-/
@[expose] public section

section

open groupHomology.IntegralBar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Convexity
open scoped Simplicial
universe u

namespace Quillen.LocalCoefficients
namespace SingularBar

variable {P : Type u} [TopologicalSpace P]

/-- The actual oriented simplex edge, as an arrow of the original fundamental groupoid. -/
def edge {n : ℕ} (σ : SingularSimplex P ⦋n⦌) (i j : Fin (n + 1)) :
    FundamentalGroupoid.mk (σ (StdSimplex.single i)) ⟶
      FundamentalGroupoid.mk (σ (StdSimplex.single j)) :=
  Path.Homotopic.Quotient.mk ((simplexEdgePath i j).map σ.continuous)

/-- Every simplex triangle commutes by the actual convex path homotopy. -/
theorem edge_comp {n : ℕ} (σ : SingularSimplex P ⦋n⦌) (i j k : Fin (n + 1)) :
    edge σ i j ≫ edge σ j k = edge σ i k := by
  change Path.Homotopic.Quotient.mk
    (((simplexEdgePath i j).map σ.continuous).trans
      ((simplexEdgePath j k).map σ.continuous)) = _
  rw [← Path.map_trans]
  exact Quotient.sound ((stdSimplex_paths_homotopic
    ((simplexEdgePath i j).trans (simplexEdgePath j k))
    (simplexEdgePath i k)).map σ)

/-- Repeated vertices give the actual identity arrow. -/
theorem edge_self {n : ℕ} (σ : SingularSimplex P ⦋n⦌) (i : Fin (n + 1)) :
    edge σ i i = 𝟙 _ := by
  change Path.Homotopic.Quotient.mk ((simplexEdgePath i i).map σ.continuous) =
    Path.Homotopic.Quotient.mk (Path.refl _)
  have h := (stdSimplex_paths_homotopic (simplexEdgePath i i)
    (Path.refl (StdSimplex.single i))).map σ
  have hr : (Path.refl (StdSimplex.single i)).map σ.continuous =
      Path.refl (σ (StdSimplex.single i)) := by
    ext t
    rfl
  rw [hr] at h
  exact Quotient.sound h

variable [PathConnectedSpace P]

/-- An actual chosen vertex path, fixed to the constant path at the basepoint. -/
def vertexPath (p x : P) : Path p x := by
  classical
  exact if h : x = p then (Path.refl p).cast rfl h else PathConnectedSpace.somePath p x

/-- The chosen path at the original basepoint is exactly the constant path. -/
theorem vertexPath_self (p : P) : vertexPath p p = Path.refl p := by
  simp [vertexPath]

/-- The actual based-loop class of a path, with the chosen vertex paths retained. -/
def basedPathLabel (p : P) {x y : P} (q : Path x y) : FundamentalGroup P p :=
  Path.Homotopic.Quotient.mk (vertexPath p x) ≫
    Path.Homotopic.Quotient.mk q ≫ Groupoid.inv (Path.Homotopic.Quotient.mk (vertexPath p y))

/-- Pointwise equality of actual paths, including their endpoints, preserves the based label. -/
theorem basedPathLabel_congr (p : P) {x y x' y' : P} (q : Path x y) (q' : Path x' y')
    (h : ∀ t, q t = q' t) : basedPathLabel p q = basedPathLabel p q' := by
  have hx : x = x' := q.source.symm.trans ((h 0).trans q'.source)
  have hy : y = y' := q.target.symm.trans ((h 1).trans q'.target)
  subst x' y'
  have hq : q = q' := by
    ext t
    exact h t
  rw [hq]

/-- The based class of a constant path is exactly the original group identity. -/
theorem basedPathLabel_refl (p x : P) : basedPathLabel p (Path.refl x) = 1 := by
  let b : FundamentalGroupoid.mk p ⟶ FundamentalGroupoid.mk x :=
    Path.Homotopic.Quotient.mk (vertexPath p x)
  change b ≫ (𝟙 _) ≫ Groupoid.inv b = 𝟙 _
  simp only [Category.id_comp, Groupoid.comp_inv]

/-- On a path already based at p, the chosen vertex paths disappear literally. -/
theorem basedPathLabel_loop (p : P) (q : Path p p) :
    basedPathLabel p q = Path.Homotopic.Quotient.mk q := by
  unfold basedPathLabel
  rw [vertexPath_self]
  change (𝟙 (FundamentalGroupoid.mk p)) ≫ Path.Homotopic.Quotient.mk q ≫
    Groupoid.inv (𝟙 (FundamentalGroupoid.mk p)) = _
  simp only [Groupoid.inv_eq_inv, IsIso.inv_id, Category.comp_id, Category.id_comp]

/-- The reverse based-edge loop as an element of the original fundamental group. -/
def fundamentalLabel (p : P) {n : ℕ} (σ : SingularSimplex P ⦋n⦌)
    (i j : Fin (n + 1)) : FundamentalGroup P p :=
  Path.Homotopic.Quotient.mk (vertexPath p (σ (StdSimplex.single j))) ≫
    edge σ j i ≫
      Groupoid.inv (Path.Homotopic.Quotient.mk (vertexPath p (σ (StdSimplex.single i))))

/-- Native multiplication reverses categorical composition, fixing this tuple order. -/
theorem fundamentalLabel_mul (p : P) {n : ℕ} (σ : SingularSimplex P ⦋n⦌)
    (i j k : Fin (n + 1)) :
    fundamentalLabel p σ i j * fundamentalLabel p σ j k =
      fundamentalLabel p σ i k := by
  change fundamentalLabel p σ j k ≫ fundamentalLabel p σ i j = _
  simp only [fundamentalLabel, Groupoid.inv_eq_inv, Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← Category.assoc (edge σ k j) (edge σ j i), edge_comp]

/-- The label retains an actual reversed based path representative. -/
theorem fundamentalLabel_eq_mk (p : P) {n : ℕ} (σ : SingularSimplex P ⦋n⦌)
    (i j : Fin (n + 1)) :
    fundamentalLabel p σ i j = Path.Homotopic.Quotient.mk
      ((vertexPath p (σ (StdSimplex.single j))).trans
        (((simplexEdgePath j i).map σ.continuous).trans
          (vertexPath p (σ (StdSimplex.single i))).symm)) := by
  rfl

/-- Every simplicial restriction retains its original two selected vertices and edge. -/
theorem fundamentalLabel_restrict (p : P) {m n : ℕ}
    (σ : SingularSimplex P ⦋n⦌) (α : ⦋m⦌ ⟶ ⦋n⦌) (i j : Fin (m + 1)) :
    fundamentalLabel p (restrictSimplex σ α) i j = fundamentalLabel p σ (α i) (α j) := by
  change basedPathLabel p ((simplexEdgePath j i).map
    (restrictSimplex σ α).continuous) =
      basedPathLabel p ((simplexEdgePath (α j) (α i)).map σ.continuous)
  apply basedPathLabel_congr
  intro t
  change σ ((simplexEdgePoint j i t).map α) =
    σ (simplexEdgePoint (α j) (α i) t)
  apply congrArg σ
  unfold simplexEdgePoint
  rw [StdSimplex.map_map]
  congr 1
  funext l
  split_ifs <;> rfl

/-- Constant simplices retain the actual identity label rather than being removed. -/
theorem fundamentalLabel_const (p x : P) {n : ℕ} (i j : Fin (n + 1)) :
    fundamentalLabel p (ContinuousMap.const _ x : SingularSimplex P ⦋n⦌) i j = 1 := by
  change basedPathLabel p ((simplexEdgePath j i).map
    (ContinuousMap.const _ x).continuous) = 1
  exact (basedPathLabel_congr p _ (Path.refl x) (fun _ ↦ rfl)).trans
    (basedPathLabel_refl p x)

/-- A repeated vertex has identity based label, including its actual anchor. -/
theorem fundamentalLabel_self (p : P) {n : ℕ}
    (σ : SingularSimplex P ⦋n⦌) (i : Fin (n + 1)) : fundamentalLabel p σ i i = 1 := by
  change Path.Homotopic.Quotient.mk (vertexPath p (σ (StdSimplex.single i))) ≫
    edge σ i i ≫ Groupoid.inv
      (Path.Homotopic.Quotient.mk (vertexPath p (σ (StdSimplex.single i)))) = 𝟙 _
  rw [edge_self, Category.id_comp, Groupoid.comp_inv]

/-- The label in the actual native Pi-one group, in the same universe as the space. -/
def label (p : P) {n : ℕ} (σ : SingularSimplex P ⦋n⦌) (i j : Fin (n + 1)) :
    HomotopyGroup.Pi 1 P p :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm (fundamentalLabel p σ i j)

/-- The original Pi-one labels obey the native inhomogeneous bar product. -/
theorem label_mul (p : P) {n : ℕ} (σ : SingularSimplex P ⦋n⦌)
    (i j k : Fin (n + 1)) :
    label p σ i j * label p σ j k = label p σ i k := by
  simp only [label, ← map_mul, fundamentalLabel_mul]

/-- Simplicial restriction keeps the same actual Pi-one label. -/
theorem label_restrict (p : P) {m n : ℕ}
    (σ : SingularSimplex P ⦋n⦌) (α : ⦋m⦌ ⟶ ⦋n⦌) (i j : Fin (m + 1)) :
    label p (restrictSimplex σ α) i j = label p σ (α i) (α j) := by
  rw [label, fundamentalLabel_restrict]
  rfl

/-- The label of a constant simplex is exactly the original Pi-one identity. -/
theorem label_const (p x : P) {n : ℕ} (i j : Fin (n + 1)) :
    label p (ContinuousMap.const _ x : SingularSimplex P ⦋n⦌) i j = 1 := by
  rw [label, fundamentalLabel_const, map_one]


/-- An actual forward based edge is the inverse of its displayed bar label. -/
theorem label_of_forwardPath (p : P) {n : ℕ} (σ : SingularSimplex P ⦋n⦌)
    (i j : Fin (n + 1)) (q : Path p p)
    (h : ∀ t, ((simplexEdgePath i j).map σ.continuous) t = q t) :
    label p σ i j =
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (Path.Homotopic.Quotient.mk q))⁻¹ := by
  have hf : fundamentalLabel p σ j i = Path.Homotopic.Quotient.mk q :=
    (basedPathLabel_congr p _ q h).trans (basedPathLabel_loop p q)
  have he := fundamentalLabel_mul p σ i j i
  rw [hf, fundamentalLabel_self] at he
  rw [label, (mul_eq_one_iff_eq_inv).mp he, map_inv]


open groupHomology.IntegralBar

/-- The actual one-chain map, including the original constant-edge generator. -/
def oneMap (p : P) :
    chainModule (constant P integralCoefficientModule.{u}) ⦋1⦌ ⟶
      (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).X₃ :=
  integralChainEvaluation 1 (fun σ ↦ Finsupp.single (label p σ 0 1) 1)

/-- The actual two-chain map, with consecutive labels in native bar order. -/
def twoMap (p : P) :
    chainModule (constant P integralCoefficientModule.{u}) ⦋2⦌ ⟶
      (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).X₂ :=
  integralChainEvaluation 2 (fun σ ↦ Finsupp.single (label p σ 0 1, label p σ 1 2) 1)

/-- The actual three-chain map, preserving all original bar triples. -/
def threeMap (p : P) :
    chainModule (constant P integralCoefficientModule.{u}) ⦋3⦌ ⟶
      (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).X₁ :=
  integralChainEvaluation 3 (fun σ ↦
    Finsupp.single (label p σ 0 1, label p σ 1 2, label p σ 2 3) 1)

/-- A singular triangle has exactly the native two-bar boundary, with all three faces. -/
theorem two_boundary_single (p : P) (σ : SingularSimplex P ⦋2⦌) :
    (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).g
      (Finsupp.single (label p σ 0 1, label p σ 1 2) (1 : ULift.{u} ℤ)) =
    ∑ i : Fin 3, (-1 : ℤ) ^ i.val •
      Finsupp.single (label p (restrictSimplex σ (SimplexCategory.δ i)) 0 1)
        (1 : ULift.{u} ℤ) := by
  rw [integerBar_dTwo_single, label_mul]
  norm_num [Fin.sum_univ_succ, label_restrict, SimplexCategory.coe_δ, Fin.succAbove, pow_succ]
  abel

/-- A singular tetrahedron has exactly the native three-bar boundary in the same order. -/
theorem three_boundary_single (p : P) (σ : SingularSimplex P ⦋3⦌) :
    (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).f
      (Finsupp.single (label p σ 0 1, label p σ 1 2, label p σ 2 3)
        (1 : ULift.{u} ℤ)) =
    ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
      Finsupp.single
        (label p (restrictSimplex σ (SimplexCategory.δ i)) 0 1,
          label p (restrictSimplex σ (SimplexCategory.δ i)) 1 2)
        (1 : ULift.{u} ℤ) := by
  rw [integerBar_dThree_single, label_mul, label_mul]
  norm_num [Fin.sum_univ_succ, label_restrict, SimplexCategory.coe_δ, Fin.succAbove, pow_succ]
  abel

/-- Evaluation on an original two-simplex keeps its coefficient and ordered labels. -/
theorem twoMap_inclusion (p : P) (σ : SingularSimplex P ⦋2⦌) (b : ULift.{u} ℤ) :
    twoMap p (chainInclusion (constant P integralCoefficientModule.{u}) σ b) =
      b.down • Finsupp.single (label p σ 0 1, label p σ 1 2) (1 : ULift.{u} ℤ) :=
  integralChainEvaluation_inclusion 2
    (G := HomotopyGroup.Pi 1 P p × HomotopyGroup.Pi 1 P p →₀ ULift.{u} ℤ) _ σ b

/-- Evaluation on an original three-simplex keeps its original ordered triple. -/
theorem threeMap_inclusion (p : P) (σ : SingularSimplex P ⦋3⦌) (b : ULift.{u} ℤ) :
    threeMap p (chainInclusion (constant P integralCoefficientModule.{u}) σ b) =
      b.down • Finsupp.single (label p σ 0 1, label p σ 1 2, label p σ 2 3)
        (1 : ULift.{u} ℤ) :=
  integralChainEvaluation_inclusion 3
    (G := HomotopyGroup.Pi 1 P p × HomotopyGroup.Pi 1 P p × HomotopyGroup.Pi 1 P p →₀
      ULift.{u} ℤ) _ σ b

/-- One-chain evaluation retains the original singular boundary signs. -/
theorem oneMap_boundary (p : P) (σ : SingularSimplex P ⦋2⦌) (b : ULift.{u} ℤ) :
    oneMap p ((singularChainComplex (constant P integralCoefficientModule.{u})).d 2 1
      (chainInclusion (constant P integralCoefficientModule.{u}) σ b)) =
    ∑ i : Fin 3, (-1 : ℤ) ^ i.val •
      (b.down • Finsupp.single (label p (restrictSimplex σ (SimplexCategory.δ i)) 0 1)
        (1 : ULift.{u} ℤ)) :=
  integralChainEvaluation_boundary 1
    (G := HomotopyGroup.Pi 1 P p →₀ ULift.{u} ℤ) _ σ b

/-- Two-chain evaluation retains the original singular boundary signs. -/
theorem twoMap_boundary (p : P) (σ : SingularSimplex P ⦋3⦌) (b : ULift.{u} ℤ) :
    twoMap p ((singularChainComplex (constant P integralCoefficientModule.{u})).d 3 2
      (chainInclusion (constant P integralCoefficientModule.{u}) σ b)) =
    ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
      (b.down • Finsupp.single
        (label p (restrictSimplex σ (SimplexCategory.δ i)) 0 1,
          label p (restrictSimplex σ (SimplexCategory.δ i)) 1 2)
        (1 : ULift.{u} ℤ)) :=
  integralChainEvaluation_boundary 2
    (G := HomotopyGroup.Pi 1 P p × HomotopyGroup.Pi 1 P p →₀ ULift.{u} ℤ) _ σ b

/-- The original degree-two differential commutes with the displayed one- and two-chain maps. -/
theorem twoMap_comm (p : P) :
    twoMap p ≫ (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).g =
      (singularChainComplex (constant P integralCoefficientModule.{u})).d 2 1 ≫ oneMap p := by
  apply Sigma.hom_ext
  intro σ
  ext b
  change (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).g
      (twoMap p (chainInclusion (constant P integralCoefficientModule.{u}) σ b)) =
    oneMap p ((singularChainComplex (constant P integralCoefficientModule.{u})).d 2 1
      (chainInclusion (constant P integralCoefficientModule.{u}) σ b))
  rw [twoMap_inclusion, map_zsmul, two_boundary_single, oneMap_boundary, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

/-- The original degree-three differential commutes with the displayed two- and three-chain maps. -/
theorem threeMap_comm (p : P) :
    threeMap p ≫ (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).f =
      (singularChainComplex (constant P integralCoefficientModule.{u})).d 3 2 ≫ twoMap p := by
  apply Sigma.hom_ext
  intro σ
  ext b
  change (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).f
      (threeMap p (chainInclusion (constant P integralCoefficientModule.{u}) σ b)) =
    twoMap p ((singularChainComplex (constant P integralCoefficientModule.{u})).d 3 2
      (chainInclusion (constant P integralCoefficientModule.{u}) σ b))
  rw [threeMap_inclusion, map_zsmul, three_boundary_single, twoMap_boundary, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

/-- A genuine morphism from the original singular H-two short complex to the native bar one. -/
def shortComplexMapCore (p : P) :
    (singularChainComplex (constant P integralCoefficientModule.{u})).sc' 3 2 1 ⟶
      integerBarShortComplex (HomotopyGroup.Pi 1 P p) where
  τ₁ := threeMap p
  τ₂ := twoMap p
  τ₃ := oneMap p
  comm₁₂ := threeMap_comm p
  comm₂₃ := twoMap_comm p

/-- The original short-complex indexing is compared by its canonical degree isomorphism. -/
def shortComplexMap (p : P) :
    (singularChainComplex (constant P integralCoefficientModule.{u})).sc 2 ⟶
      integerBarShortComplex (HomotopyGroup.Pi 1 P p) :=
  ((singularChainComplex (constant P integralCoefficientModule.{u})).isoSc' 3 2 1
    (ChainComplex.prev ℕ 2) (ChainComplex.next_nat_succ 1)).hom ≫ shortComplexMapCore p

/-- The middle component of the canonical indexing comparison is the original two-chain map. -/
theorem shortComplexMap_τ₂ (p : P) : (shortComplexMap p).τ₂ = twoMap p := by
  change (𝟙 _) ≫ twoMap p = twoMap p
  exact Category.id_comp _

/-- The induced map on the original integral singular H-two and actual native bar homology. -/
def hTwoMap (p : P) : homology (constant P integralCoefficientModule.{u}) 2 ⟶
    integerBarH2 (HomotopyGroup.Pi 1 P p) :=
  ShortComplex.homologyMap (shortComplexMap p)

/-- On an actual cycle the H-two map is the class of the displayed original two-chain map. -/
theorem hTwoMap_class (p : P)
    (c : (singularChainComplex (constant P integralCoefficientModule.{u})).cycles 2) :
    hTwoMap p ((singularChainComplex (constant P integralCoefficientModule.{u})).homologyπ 2 c) =
      (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).homologyπ
        (ShortComplex.cyclesMap (shortComplexMap p) c) :=
  ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality (shortComplexMap p)) c

/-- The target cycle has exactly the two-chain image, with no chosen quotient representative. -/
theorem hTwoMap_cycle_val (p : P)
    (c : (singularChainComplex (constant P integralCoefficientModule.{u})).cycles 2) :
    (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).iCycles
        (ShortComplex.cyclesMap (shortComplexMap p) c) =
      twoMap p ((singularChainComplex (constant P integralCoefficientModule.{u})).iCycles 2 c) :=
  by
    have h := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i (shortComplexMap p)) c
    change (integerBarShortComplex (HomotopyGroup.Pi 1 P p)).iCycles
      (ShortComplex.cyclesMap (shortComplexMap p) c) =
        (shortComplexMap p).τ₂
          ((singularChainComplex (constant P integralCoefficientModule.{u})).iCycles 2 c) at h
    rw [shortComplexMap_τ₂] at h
    exact h

/-- The comparison on mathlib's original integral singular homology uses its existing reindexing. -/
def singularH2Map (p : P) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) 2).obj
      integralCoefficientModule.{u}).obj (TopCat.of P) ⟶
        integerBarH2 (HomotopyGroup.Pi 1 P p) :=
  (constantHomologyIso integralCoefficientModule.{u} 2).inv ≫ hTwoMap p

end SingularBar
end Quillen.LocalCoefficients

end
