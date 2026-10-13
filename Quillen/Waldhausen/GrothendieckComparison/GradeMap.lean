/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Cofinality.GradedGroupNerve
public import Quillen.Waldhausen.Cofinality.GradedRealization
public import Quillen.Waldhausen.Functoriality.KMap
public import Quillen.Topology.ClassifyingSpace.FundamentalGroup
public import Quillen.Waldhausen.GrothendieckGroup.Basic

/-!
# Original additive gradings on genuine fine Waldhausen K₀

An original additive object grading defines a simplicial map from the actual
fine S-construction to the nerve of its full group of values. Unlike the
comparison with the realized value range, this construction requires no
factorization, realization-surjectivity or fibration hypothesis. Applied to
the original object/weak-arrow/pushout quotient, it gives the canonical
homotopical-to-classical homomorphism. Bijectivity is not asserted here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.Cofinality.Grading
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

/-- The original realized interval grades define group-nerve arrows without
requiring every group element to be represented by an object. -/
def rowGradeNerveMap : d.gradeSSet ⟶ nerve (SingleObj (Multiplicative G)) where
  app n := TypeCat.ofHom (d.rowGradeChain n.unop)
  naturality n m α := by
    ext a : 3
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual fine S-construction maps to the full original grading group. -/
def fineGradeNerveMap : sSet W.cof W.weq ⟶ nerve (SingleObj (Multiplicative G)) :=
  sSetMap (Fibration.changeWeak_exact d.nested) ≫ d.gradeMap ≫ d.rowGradeNerveMap

/-- Every group-nerve arrow is exactly the grade of the original first-row interval. -/
@[simp] theorem fineGradeNerveMap_component (n : SimplexCategory)
    (X : (sSet W.cof W.weq).obj (op n)) (p : Interval n) :
    Multiplicative.toAdd
      (((d.fineGradeNerveMap).app (op n) X).map (homOfLE p.property)) =
        d.value (X.val.obj (0, p)) := rfl

/-- The actual chosen zero simplex goes to the unique original group vertex. -/
theorem fineGradeNerveMap_zero_vertex :
    d.fineGradeNerveMap.app (op ⦋0⦌)
      (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) =
        nerveVertex (SingleObj.star (Multiplicative G)) := by
  apply ComposableArrows.ext₀
  exact Subsingleton.elim _ _

/-- The unchanged realized grading map preserves the actual chosen basepoint. -/
theorem fineGradeNerveMap_basepoint :
    (SSet.toTop.map d.fineGradeNerveMap).hom W.kBasepoint =
      classifyingSpacePoint (SingleObj.star (Multiplicative G)) := by
  change SSet.toTop.map d.fineGradeNerveMap
    (realizationPoint (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌))) = _
  rw [realizationPoint_naturality, d.fineGradeNerveMap_zero_vertex]
  rfl

/-- The based map of actual homotopy groups induced by the original fine grading map. -/
def fineKZeroToGroupPi : W.K 0 →*
    HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj (Multiplicative G)))
      (classifyingSpacePoint (SingleObj.star (Multiplicative G))) :=
  homotopyGroupMapHom (SSet.toTop.map d.fineGradeNerveMap).hom
    d.fineGradeNerveMap_basepoint

/-- The original fine homotopical K₀ has a grading in the full original value group. -/
def fineKZeroMap : W.K 0 →* Multiplicative G :=
  (GroupoidClassifying.singleObjPiOneEquiv (Multiplicative G)).symm.toMonoidHom.comp
    d.fineKZeroToGroupPi

end Quillen.Waldhausen.Cofinality.Grading

namespace Quillen.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- The canonical map from genuine fine Waldhausen K₀ to the original classical
object/weak-equivalence/cofibration-pushout presentation, with no factorization premise. -/
def kZeroToGrothendieck : W.K 0 →* Multiplicative (Group W) :=
  (grading W).fineKZeroMap

end Quillen.Waldhausen.AlgebraicGrothendieck
