/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeTree
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionWholeReferenceAttachments

/-!
# The actual Laurent map of the four-edge polynomial span

Four successive original simplicial pushouts glue the unchanged normalization and geometric
edges. Both exterior maps act on every polynomial-reference node. The resulting map retains
all four full cylinders and both entire polynomial chart summands.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
attribute [local irreducible] boundedFlatNormalizedPullback

theorem descend_square {X Y Z K : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (l : Y ⟶ K) (r : Z ⟶ K) (H : X ⊗ Δ[1] ⟶ K)
    (h₀ : SSet.ι₀ ≫ H = f ≫ l) (h₁ : SSet.ι₁ ≫ H = g ≫ r) :
    DoubleCylinder.simplicialEndpoints X ≫ H = coprod.map f g ≫ coprod.desc l r := by
  apply coprod.hom_ext
  · simpa [DoubleCylinder.simplicialEndpoints, Category.assoc] using h₀
  · simpa [DoubleCylinder.simplicialEndpoints, Category.assoc] using h₁

/-- Descend a complete cylinder and both whole endpoint maps through its displayed pushout. -/
def descend {X Y Z K : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (l : Y ⟶ K) (r : Z ⟶ K) (H : X ⊗ Δ[1] ⟶ K)
    (h₀ : SSet.ι₀ ≫ H = f ≫ l) (h₁ : SSet.ι₁ ≫ H = g ≫ r) :
    DoubleCylinder.simplicial f g ⟶ K :=
  (DoubleCylinder.simplicial_isPushout f g).desc H (coprod.desc l r)
    (descend_square f g l r H h₀ h₁)

theorem descend_cylinder {X Y Z K : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (l : Y ⟶ K) (r : Z ⟶ K) (H : X ⊗ Δ[1] ⟶ K)
    (h₀ : SSet.ι₀ ≫ H = f ≫ l) (h₁ : SSet.ι₁ ≫ H = g ≫ r) :
    DoubleCylinder.simplicialCylinder f g ≫ descend f g l r H h₀ h₁ = H :=
  (DoubleCylinder.simplicial_isPushout f g).inl_desc _ _ _

theorem descend_left {X Y Z K : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (l : Y ⟶ K) (r : Z ⟶ K) (H : X ⊗ Δ[1] ⟶ K)
    (h₀ : SSet.ι₀ ≫ H = f ≫ l) (h₁ : SSet.ι₁ ≫ H = g ≫ r) :
    FourEdgeTree.left f g ≫ descend f g l r H h₀ h₁ = l := by
  change coprod.inl ≫
    (DoubleCylinder.simplicialEnds f g ≫ descend f g l r H h₀ h₁) = l
  rw [descend, (DoubleCylinder.simplicial_isPushout f g).inr_desc, coprod.inl_desc]

theorem descend_right {X Y Z K : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (l : Y ⟶ K) (r : Z ⟶ K) (H : X ⊗ Δ[1] ⟶ K)
    (h₀ : SSet.ι₀ ≫ H = f ≫ l) (h₁ : SSet.ι₁ ≫ H = g ≫ r) :
    FourEdgeTree.right f g ≫ descend f g l r H h₀ h₁ = r := by
  change coprod.inr ≫
    (DoubleCylinder.simplicialEnds f g ≫ descend f g l r H h₀ h₁) = r
  rw [descend, (DoubleCylinder.simplicial_isPushout f g).inr_desc, coprod.inr_desc]

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => normalizedMap (polynomialProjection P a)
local notation "F" => reference P a E

/-- Each intermediate vertex retains the corresponding original full projection node. -/
def vertexMap (j : Fin 5) : parameterSSet E ⟶ parameterSSet F :=
  nerveMap (Codiscrete.functorOfFun (fun e ↦ nodes P a E e j))

/-- A literal two-node edge of the original five-node diagram, over the whole input nerve. -/
def edgeMap (i j : Fin 5) : parameterSSet E ⊗ Δ[1] ⟶ parameterSSet F :=
  FiniteParameter.simplicial E F (fun e k ↦ nodes P a E e (![i, j] k))

/-- The original ordered two-vertex face inside the five-node projection simplex. -/
def edgeFace (i j : Fin 5) (hij : i ≤ j) : ⦋1⦌ ⟶ ⦋4⦌ :=
  SimplexCategory.Hom.mk ⟨![i, j], by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all⟩

/-- Each cylinder is literally the restriction of the whole five-node simplicial family. -/
theorem edgeMap_restriction (i j : Fin 5) (hij : i ≤ j) :
    parameterSSet E ◁ SSet.stdSimplex.map (edgeFace i j hij) ≫
      FiniteParameter.simplicial E F (nodes P a E) = edgeMap P a E i j :=
  FiniteParameter.simplicial_restrict E F (nodes P a E) (edgeFace i j hij)

@[reassoc]
theorem edgeMap_zero (i j : Fin 5) : SSet.ι₀ ≫ edgeMap P a E i j = vertexMap P a E i :=
  FiniteParameter.simplicial_zero E F (fun e k ↦ nodes P a E e (![i, j] k))

@[reassoc]
theorem edgeMap_one (i j : Fin 5) : SSet.ι₁ ≫ edgeMap P a E i j = vertexMap P a E j :=
  FiniteParameter.simplicial_one E F (fun e k ↦ nodes P a E e (![i, j] k))

/-- The chart map acts before any restriction to coefficient-to-polynomial inputs. -/
def chartMap (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    parameterSSet (E ≫ J) ⟶ parameterSSet F :=
  nerveMap (Codiscrete.functorOfFun (chartAttachmentNode P a E α ha))

/-- The entire simplicial attachment uses the proved full polynomial endpoint factorization. -/
theorem attachment_chartMap
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (j : Fin 5)
    (hj : BassProjectionPath.nodes P a j =
      ⟨BassMJoin.endpointMap (c := a) P α, BassMJoin.projectionEndpointIso (c := a) P α ha⟩) :
    FourEdgeTree.attachment E J ≫ chartMap P a E α ha = vertexMap P a E j := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · change Codiscrete.mk
      (chartAttachmentNode P a E α ha (polynomialNode P a E (c.obj i).as)) =
        Codiscrete.mk (nodes P a E (c.obj i).as j)
    exact congrArg Codiscrete.mk
      ((chartAttachmentNode_polynomialNode P a E α ha (c.obj i).as).trans
        (nodes_endpoint P a E α ha j hj (c.obj i).as).symm)
  · intro i j g
    apply Subsingleton.elim

/-- The positive normalization branch on its entire original pushout. -/
def firstMap : FourEdgeTree.first E J ⟶ parameterSSet F :=
  descend (𝟙 _) (FourEdgeTree.attachment E J) (vertexMap P a E 1)
    (chartMap P a E (underToLaurent R) (laurentPlus_projection P a)) (edgeMap P a E 1 2)
    (by simpa only [Category.id_comp] using edgeMap_zero P a E 1 2)
    ((edgeMap_one P a E 1 2).trans
      (attachment_chartMap P a E (underToLaurent R) (laurentPlus_projection P a) 2
        (BassMJoin.plus_endpoint_node P)).symm)

theorem firstMap_one : FourEdgeTree.firstOne E J ≫ firstMap P a E = vertexMap P a E 1 :=
  descend_left _ _ _ _ _ _ _
theorem firstMap_plus : FourEdgeTree.firstPlus E J ≫ firstMap P a E =
    chartMap P a E (underToLaurent R) (laurentPlus_projection P a) :=
  descend_right _ _ _ _ _ _ _
theorem firstMap_edge :
    DoubleCylinder.simplicialCylinder (𝟙 _) (FourEdgeTree.attachment E J) ≫ firstMap P a E =
      edgeMap P a E 1 2 := descend_cylinder _ _ _ _ _ _ _

/-- Attach the positive geometric cylinder to the complete first branch. -/
def secondMap : FourEdgeTree.second E J ⟶ parameterSSet F :=
  descend (𝟙 _) (FourEdgeTree.firstOne E J) (vertexMap P a E 0) (firstMap P a E)
    (edgeMap P a E 0 1)
    (by simpa only [Category.id_comp] using edgeMap_zero P a E 0 1)
    ((edgeMap_one P a E 0 1).trans (firstMap_one P a E).symm)

theorem secondMap_zero :
    FourEdgeTree.secondZero E J ≫ secondMap P a E = vertexMap P a E 0 :=
  descend_left _ _ _ _ _ _ _
theorem secondMap_first :
    FourEdgeTree.firstInSecond E J ≫ secondMap P a E = firstMap P a E :=
  descend_right _ _ _ _ _ _ _
theorem secondMap_edge :
    DoubleCylinder.simplicialCylinder (𝟙 _) (FourEdgeTree.firstOne E J) ≫ secondMap P a E =
      edgeMap P a E 0 1 := descend_cylinder _ _ _ _ _ _ _

/-- Attach the inverse geometric cylinder without collapsing either preceding branch. -/
def thirdMap : FourEdgeTree.third E J ⟶ parameterSSet F :=
  descend (FourEdgeTree.secondZero E J) (𝟙 _) (secondMap P a E) (vertexMap P a E 3)
    (edgeMap P a E 0 3)
    ((edgeMap_zero P a E 0 3).trans (secondMap_zero P a E).symm)
    (by simpa only [Category.id_comp] using edgeMap_one P a E 0 3)

theorem thirdMap_second :
    FourEdgeTree.secondInThird E J ≫ thirdMap P a E = secondMap P a E :=
  descend_left _ _ _ _ _ _ _
theorem thirdMap_three :
    FourEdgeTree.thirdThree E J ≫ thirdMap P a E = vertexMap P a E 3 :=
  descend_right _ _ _ _ _ _ _
theorem thirdMap_edge :
    DoubleCylinder.simplicialCylinder (FourEdgeTree.secondZero E J) (𝟙 _) ≫ thirdMap P a E =
      edgeMap P a E 0 3 := descend_cylinder _ _ _ _ _ _ _

/-- The actual Laurent map glues all four unchanged original reference edges. -/
def beta : FourEdgeTree.simplicial E J ⟶ parameterSSet F :=
  descend (FourEdgeTree.thirdThree E J) (FourEdgeTree.attachment E J) (thirdMap P a E)
    (chartMap P a E (underToLaurentInvert R) (laurentMinus_projection P a)) (edgeMap P a E 3 4)
    ((edgeMap_zero P a E 3 4).trans (thirdMap_three P a E).symm)
    ((edgeMap_one P a E 3 4).trans
      (attachment_chartMap P a E (underToLaurentInvert R) (laurentMinus_projection P a) 4
        (BassMJoin.minus_endpoint_node P)).symm)

theorem beta_third : FourEdgeTree.thirdInTree E J ≫ beta P a E = thirdMap P a E :=
  descend_left _ _ _ _ _ _ _
theorem beta_second : FourEdgeTree.secondInTree E J ≫ beta P a E = secondMap P a E := by
  rw [FourEdgeTree.secondInTree, Category.assoc, beta_third, thirdMap_second]
theorem beta_first : FourEdgeTree.firstInTree E J ≫ beta P a E = firstMap P a E := by
  rw [FourEdgeTree.firstInTree, Category.assoc, beta_second, secondMap_first]

@[reassoc]
theorem beta_plus : FourEdgeTree.plusVertex E J ≫ beta P a E =
    chartMap P a E (underToLaurent R) (laurentPlus_projection P a) := by
  rw [FourEdgeTree.plusVertex, Category.assoc, beta_first, firstMap_plus]

@[reassoc]
theorem beta_minus : FourEdgeTree.minusVertex E J ≫ beta P a E =
    chartMap P a E (underToLaurentInvert R) (laurentMinus_projection P a) :=
  descend_right _ _ _ _ _ _ _

@[reassoc]
theorem beta_zero : FourEdgeTree.zeroVertex E J ≫ beta P a E = vertexMap P a E 0 := by
  rw [FourEdgeTree.zeroVertex, Category.assoc, beta_second, secondMap_zero]

@[reassoc]
theorem beta_one : FourEdgeTree.oneVertex E J ≫ beta P a E = vertexMap P a E 1 := by
  rw [FourEdgeTree.oneVertex, Category.assoc, beta_first, firstMap_one]

@[reassoc]
theorem beta_three : FourEdgeTree.threeVertex E J ≫ beta P a E = vertexMap P a E 3 := by
  rw [FourEdgeTree.threeVertex, Category.assoc, beta_third, thirdMap_three]

@[reassoc]
theorem beta_edge12 : FourEdgeTree.edge12 E J ≫ beta P a E = edgeMap P a E 1 2 := by
  rw [FourEdgeTree.edge12, Category.assoc, beta_first, firstMap_edge]

@[reassoc]
theorem beta_edge01 : FourEdgeTree.edge01 E J ≫ beta P a E = edgeMap P a E 0 1 := by
  rw [FourEdgeTree.edge01, Category.assoc, beta_second, secondMap_edge]

@[reassoc]
theorem beta_edge03 : FourEdgeTree.edge03 E J ≫ beta P a E = edgeMap P a E 0 3 := by
  rw [FourEdgeTree.edge03, Category.assoc, beta_third, thirdMap_edge]

@[reassoc]
theorem beta_edge34 : FourEdgeTree.edge34 E J ≫ beta P a E = edgeMap P a E 3 4 :=
  descend_cylinder _ _ _ _ _ _ _

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
