/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCarrier
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveWhiskering

/-! The four original oriented reference edges and their unreduced Laurent mapping cone. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
open CutOpenCarrier

/-- Original left summand of an actual simplicial double cylinder. -/
def left {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z) :
    Y ⟶ DoubleCylinder.simplicial f g :=
  coprod.inl ≫ DoubleCylinder.simplicialEnds f g

/-- Original right summand, without identifying its points with the left summand. -/
def right {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z) :
    Z ⟶ DoubleCylinder.simplicial f g :=
  coprod.inr ≫ DoubleCylinder.simplicialEnds f g

@[reassoc] theorem cylinder_zero {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z) :
    SSet.ι₀ ≫ DoubleCylinder.simplicialCylinder f g = f ≫ left f g := by
  have h := congrArg (fun k ↦ (coprod.inl : X ⟶ X ⨿ X) ≫ k)
    (DoubleCylinder.simplicial_isPushout f g).w
  simpa [DoubleCylinder.simplicialEndpoints, left, Category.assoc] using h

@[reassoc] theorem cylinder_one {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z) :
    SSet.ι₁ ≫ DoubleCylinder.simplicialCylinder f g = g ≫ right f g := by
  have h := congrArg (fun k ↦ (coprod.inr : X ⟶ X ⨿ X) ≫ k)
    (DoubleCylinder.simplicial_isPushout f g).w
  simpa [DoubleCylinder.simplicialEndpoints, right, Category.assoc] using h

variable {V W T : Model.{u}} (E : V ⟶ W) (J : W ⟶ T)

/-- The exact polynomial postcomposition on full dependent reference nodes. -/
def attachment : parameterSSet E ⟶ parameterSSet (E ≫ J) :=
  nerveMap (Codiscrete.functorOfFun (postcompNode J))

/-- Edge 1→2: the positive normalization cylinder. -/
def first : SSet.{u} := DoubleCylinder.simplicial (𝟙 (parameterSSet E)) (attachment E J)
/-- The `E`-reference inclusion into the first double cylinder. -/
def firstOne : parameterSSet E ⟶ first E J := left (𝟙 _) (attachment E J)
/-- The `E ≫ J`-reference inclusion at the plus end of the first double cylinder. -/
def firstPlus : parameterSSet (E ≫ J) ⟶ first E J := right (𝟙 _) (attachment E J)

/-- Edge 0→1: its target is the entire already-attached first branch. -/
def second : SSet.{u} := DoubleCylinder.simplicial (𝟙 (parameterSSet E)) (firstOne E J)
/-- The `E`-reference inclusion at the zero end of the second double cylinder. -/
def secondZero : parameterSSet E ⟶ second E J := left (𝟙 _) (firstOne E J)
/-- Include the entire first double cylinder into the second one. -/
def firstInSecond : first E J ⟶ second E J := right (𝟙 _) (firstOne E J)

/-- Edge 0→3: the center attaches through its original whole first branch. -/
def third : SSet.{u} := DoubleCylinder.simplicial (secondZero E J) (𝟙 (parameterSSet E))
/-- Include the entire second double cylinder into the third one. -/
def secondInThird : second E J ⟶ third E J := left (secondZero E J) (𝟙 _)
/-- The `E`-reference inclusion at the three end of the third double cylinder. -/
def thirdThree : parameterSSet E ⟶ third E J := right (secondZero E J) (𝟙 _)

/-- Edge 3→4: the negative polynomial endpoint is a separate summand. -/
def simplicial : SSet.{u} := DoubleCylinder.simplicial (thirdThree E J) (attachment E J)
/-- Include the entire third double cylinder into the complete four-edge tree. -/
def thirdInTree : third E J ⟶ simplicial E J := left (thirdThree E J) (attachment E J)
/-- The full `E ≫ J`-reference inclusion at the minus vertex of the complete tree. -/
def minusVertex : parameterSSet (E ≫ J) ⟶ simplicial E J :=
  right (thirdThree E J) (attachment E J)
/-- Include the second double cylinder through the third cylinder into the complete tree. -/
def secondInTree : second E J ⟶ simplicial E J := secondInThird E J ≫ thirdInTree E J
/-- Include the first double cylinder through the second and third into the complete tree. -/
def firstInTree : first E J ⟶ simplicial E J := firstInSecond E J ≫ secondInTree E J

/-- The full `E`-reference inclusion at vertex zero of the complete tree. -/
def zeroVertex : parameterSSet E ⟶ simplicial E J := secondZero E J ≫ secondInTree E J
/-- The full `E`-reference inclusion at vertex one of the complete tree. -/
def oneVertex : parameterSSet E ⟶ simplicial E J := firstOne E J ≫ firstInTree E J
/-- The full `E`-reference inclusion at vertex three of the complete tree. -/
def threeVertex : parameterSSet E ⟶ simplicial E J := thirdThree E J ≫ thirdInTree E J
/-- The full `E ≫ J`-reference inclusion at the plus vertex of the complete tree. -/
def plusVertex : parameterSSet (E ≫ J) ⟶ simplicial E J := firstPlus E J ≫ firstInTree E J

/-- The original oriented reference edge from vertex one to the plus vertex. -/
def edge12 : parameterSSet E ⊗ Δ[1] ⟶ simplicial E J :=
  DoubleCylinder.simplicialCylinder (𝟙 _) (attachment E J) ≫ firstInTree E J
/-- The original oriented reference edge from vertex zero to vertex one. -/
def edge01 : parameterSSet E ⊗ Δ[1] ⟶ simplicial E J :=
  DoubleCylinder.simplicialCylinder (𝟙 _) (firstOne E J) ≫ secondInTree E J
/-- The original oriented reference edge from vertex zero to vertex three. -/
def edge03 : parameterSSet E ⊗ Δ[1] ⟶ simplicial E J :=
  DoubleCylinder.simplicialCylinder (secondZero E J) (𝟙 _) ≫ thirdInTree E J
/-- The original oriented reference edge from vertex three to the minus vertex. -/
def edge34 : parameterSSet E ⊗ Δ[1] ⟶ simplicial E J :=
  DoubleCylinder.simplicialCylinder (thirdThree E J) (attachment E J)

@[reassoc] theorem edge12_zero : SSet.ι₀ ≫ edge12 E J = oneVertex E J := by
  simp [edge12, oneVertex, firstOne, secondZero, thirdThree, firstInTree, secondInTree,
    secondInThird, thirdInTree, firstInSecond, cylinder_zero_assoc, left, right, Category.assoc]
@[reassoc] theorem edge12_one : SSet.ι₁ ≫ edge12 E J = attachment E J ≫ plusVertex E J := by
  simp [edge12, plusVertex, firstOne, firstPlus, secondZero, thirdThree, firstInTree,
    secondInTree, secondInThird, thirdInTree, firstInSecond, cylinder_one_assoc, left, right,
    Category.assoc]
@[reassoc] theorem edge01_zero : SSet.ι₀ ≫ edge01 E J = zeroVertex E J := by
  simp [edge01, zeroVertex, firstOne, secondZero, thirdThree, secondInTree, secondInThird,
    thirdInTree, cylinder_zero_assoc, left, right, Category.assoc]
@[reassoc] theorem edge01_one : SSet.ι₁ ≫ edge01 E J = oneVertex E J := by
  simp [edge01, oneVertex, firstOne, secondZero, thirdThree, firstInTree, secondInTree,
    secondInThird, thirdInTree, firstInSecond, cylinder_one_assoc, left, right, Category.assoc]
@[reassoc] theorem edge03_zero : SSet.ι₀ ≫ edge03 E J = zeroVertex E J := by
  simp [edge03, zeroVertex, firstOne, secondZero, thirdThree, secondInTree, secondInThird,
    thirdInTree, cylinder_zero_assoc, left, right, Category.assoc]
@[reassoc] theorem edge03_one : SSet.ι₁ ≫ edge03 E J = threeVertex E J := by
  simp [edge03, threeVertex, firstOne, secondZero, thirdThree, thirdInTree, cylinder_one_assoc,
    left, right, Category.assoc]
@[reassoc] theorem edge34_zero : SSet.ι₀ ≫ edge34 E J = threeVertex E J := by
  simp [edge34, threeVertex, firstOne, secondZero, thirdThree, thirdInTree, cylinder_zero, left,
    right, Category.assoc]
@[reassoc] theorem edge34_one : SSet.ι₁ ≫ edge34 E J = attachment E J ≫ minusVertex E J := by
  simp [edge34, minusVertex, firstOne, secondZero, thirdThree, cylinder_one, left, right]
/-- The scalar tree retains every point of every full reference nerve. -/
abbrev space : TopCat.{u} := |simplicial E J|

private theorem reference_contractible {A B : Model.{u}} (F : A ⟶ B) :
    ContractibleSpace |parameterSSet F| :=
  (contractible_iff_id_nullhomotopic _).2
    ⟨classifyingSpacePoint (referenceNode F), ⟨(referenceContraction F).symm⟩⟩

private theorem double_contractible {X Y Z : SSet.{u}}
    [ContractibleSpace |X|] [ContractibleSpace |Y|] [ContractibleSpace |Z|]
    (f : X ⟶ Y) (g : X ⟶ Z) : ContractibleSpace |DoubleCylinder.simplicial f g| :=
  DoubleCylinder.contractibleSpace_of_contractible (SSet.toTop.map f) (SSet.toTop.map g)
    (DoubleCylinder.realized_isPushout f g)

/-- Four applications of the existing displayed-pushout theorem contract this exact tree. -/
theorem contractibleSpace : ContractibleSpace (space E J) := by
  let : ContractibleSpace |parameterSSet E| := reference_contractible E
  let : ContractibleSpace |parameterSSet (E ≫ J)| := reference_contractible (E ≫ J)
  let : ContractibleSpace |first E J| := double_contractible (𝟙 _) (attachment E J)
  let : ContractibleSpace |second E J| := double_contractible (𝟙 _) (firstOne E J)
  let : ContractibleSpace |third E J| := double_contractible (secondZero E J) (𝟙 _)
  exact double_contractible (thirdThree E J) (attachment E J)

variable {U : Model.{u}} (F : V ⟶ U)
/-- The original whole Laurent map is the cone attachment; the tree is not reduced at a node. -/
def cone (β : simplicial E J ⟶ parameterSSet F) : SSet.{u} :=
  DoubleCylinder.simplicial β (SSet.stdSimplex.isTerminalObj₀.from (simplicial E J))

/-- The Laurent-reference inclusion into the unreduced cone attached along the supplied `β`. -/
def coneLaurent (β : simplicial E J ⟶ parameterSSet F) : parameterSSet F ⟶ cone E J F β :=
  left β (SSet.stdSimplex.isTerminalObj₀.from _)
/-- The separate tip inclusion into the unreduced cone attached along the supplied `β`. -/
def coneTip (β : simplicial E J ⟶ parameterSSet F) : tipSSet ⟶ cone E J F β :=
  right β (SSet.stdSimplex.isTerminalObj₀.from _)
/-- The complete unreduced cylinder from the four-edge tree to the Laurent reference and
separate tip. -/
def coneCylinder (β : simplicial E J ⟶ parameterSSet F) :
    simplicial E J ⊗ Δ[1] ⟶ cone E J F β :=
  DoubleCylinder.simplicialCylinder β (SSet.stdSimplex.isTerminalObj₀.from _)

@[reassoc] theorem coneCylinder_zero (β : simplicial E J ⟶ parameterSSet F) :
    SSet.ι₀ ≫ coneCylinder E J F β = β ≫ coneLaurent E J F β := cylinder_zero _ _
@[reassoc] theorem coneCylinder_one (β : simplicial E J ⟶ parameterSSet F) :
    SSet.ι₁ ≫ coneCylinder E J F β =
      SSet.stdSimplex.isTerminalObj₀.from _ ≫ coneTip E J F β := cylinder_one _ _

/-- The unreduced mapping cone is contractible while retaining its whole Laurent summand. -/
theorem cone_contractibleSpace (β : simplicial E J ⟶ parameterSSet F) :
    ContractibleSpace |cone E J F β| := by
  let : ContractibleSpace |simplicial E J| := contractibleSpace E J
  let : ContractibleSpace |parameterSSet F| := reference_contractible F
  exact double_contractible β (SSet.stdSimplex.isTerminalObj₀.from _)

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
