/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCarrier
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteParameter
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceProductNodes

/-!
# Finite source parameters on the original one-sheet attachment

The original O input cap applies the fixed polynomial pair cap to a five-node polynomial
square. These two full parameter maps retain the source node, target node and exact attachment.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Convexity
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FiniteSourceSheet
open CutOpenCarrier
variable {V W T U : Model.{u}} (D : V ⟶ W) (F : W ⟶ T) (J : T ⟶ U)
variable {k : ℕ} (Z : Fin (k + 1) → Node D)

/-- The source is the entire existing first sheet of the fixed polynomial pair. -/
abbrev source := |firstSimplicial F J (F ≫ J) (Iso.refl _)|

/-- Its target has the actual source-product reference and the same chart attachment. -/
abbrev target := |firstSimplicial (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _)|

/-- Full polynomial product nodes, with the finite source factor written first. -/
def polynomialNode (M : Node F) (i : Fin (k + 1)) : Node (D ≫ F) :=
  CommonReferenceProduct.node (D ≫ F) D F (Iso.refl _) (Z i) M

/-- The Laurent product retains the displayed associator into the original chart composite. -/
def laurentNode (M : Node (F ≫ J)) (i : Fin (k + 1)) : Node ((D ≫ F) ≫ J) :=
  CommonReferenceProduct.node ((D ≫ F) ≫ J) D (F ≫ J)
    (Functor.associator D.functor F.functor J.functor) (Z i) M

/-- The existing full-node product/postcomposition interchange is the attachment square. -/
theorem attachment_node (M : Node F) (i : Fin (k + 1)) :
    laurentNode D F J Z (attachPostcompNode F J (F ≫ J) (Iso.refl _) M) i =
      attachPostcompNode (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _)
        (polynomialNode D F Z M i) := by
  exact CommonReferenceProduct.node_postcomp ((D ≫ F) ≫ J) D F J
    (Functor.associator D.functor F.functor J.functor) (Z i) M

/-- The finite source family acts continuously on every polynomial nerve point. -/
def polynomial : C(|parameterSSet F| × StdSimplex ℝ (Fin (k + 1)),
    |parameterSSet (D ≫ F)|) :=
  FiniteParameter.parameter F (D ≫ F) (polynomialNode D F Z)

/-- The same complete source family acts on the Laurent baseline. -/
def laurent : C(|parameterSSet (F ≫ J)| × StdSimplex ℝ (Fin (k + 1)),
    |parameterSSet ((D ≫ F) ≫ J)|) :=
  FiniteParameter.parameter (F ≫ J) ((D ≫ F) ≫ J) (laurentNode D F J Z)

/-- The whole attachment equation holds for every nerve point and independent simplex input. -/
theorem attachment_parameter (y : |parameterSSet F|) (z : StdSimplex ℝ (Fin (k + 1))) :
    laurent D F J Z (SSet.toTop.map (attaching F J (F ≫ J) (Iso.refl _)) y, z) =
      SSet.toTop.map (attaching (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _))
        (polynomial D F Z (y, z)) := by
  obtain ⟨m, N, w, rfl⟩ := exists_parameter F y
  change FiniteParameter.parameter _ _ (laurentNode D F J Z)
    (mapParameter (attachPostcompNode F J (F ≫ J) (Iso.refl _)) (parameter F N w), z) =
      mapParameter (attachPostcompNode (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _))
        (FiniteParameter.parameter _ _ (polynomialNode D F Z) (parameter F N w, z))
  rw [mapParameter_parameter, FiniteParameter.parameter_characteristic,
    FiniteParameter.parameter_characteristic, mapParameter_parameter]
  apply congrArg (fun ns ↦ parameter ((D ≫ F) ≫ J) ns
    (Quillen.SimplexGrid.parameter m k (w, z)))
  funext i
  exact attachment_node D F J Z (N ((Quillen.SimplexGrid.indexEquiv m k).symm i).1)
    ((Quillen.SimplexGrid.indexEquiv m k).symm i).2

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FiniteSourceSheet
