import Quillen.CategoryTheory.ArrowDiagrams
import Quillen.Waldhausen.ExtensionCategory.PostcomposeDetection
import Quillen.Waldhausen.SConstruction.Rows.PointwiseArrows
import Quillen.Waldhausen.ExtensionCategory.TriplePushout
import Quillen.Waldhausen.ExtensionCategory.Transpose
import Quillen.Waldhausen.ExtensionCategory.TransposeExact
import Quillen.Waldhausen.SConstruction.Rows.ReedyArrows
import Quillen.Waldhausen.SConstruction.Rows.JointFunctor
import Quillen.Waldhausen.Cylinder.JointExact
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.CategoryTheory.ArrowDiagrams, `Quillen.Waldhausen.ExtensionCategory.PostcomposeDetection, `Quillen.Waldhausen.SConstruction.Rows.PointwiseArrows, `Quillen.Waldhausen.ExtensionCategory.TriplePushout, `Quillen.Waldhausen.ExtensionCategory.Transpose, `Quillen.Waldhausen.ExtensionCategory.TransposeExact, `Quillen.Waldhausen.SConstruction.Rows.ReedyArrows, `Quillen.Waldhausen.SConstruction.Rows.JointFunctor]
  let mut count : Nat := 0
  for origin in targets do
    let mut subtotal : Nat := 0
    for (name, _) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      unless env.header.moduleNames[index.toNat]! == origin do continue
      count := count + 1
      subtotal := subtotal + 1
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{origin}: {name} depends on unsupported assumption {dependency}"
      logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
    logInfo m!"ORIGIN_COUNT {origin}: {subtotal}"
  unless count == 139 do throwError "Expected 139 row-arrow-interchange origins, got {count}"
  logInfo m!"Audited all {count} row-arrow-interchange declaration origins."
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v''
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.ArrowDiagrams
variable {C : Type u} [Category.{v} C] {J : Type u'} [Category.{v'} J]
example (X : Arrow (J ⥤ C)) (j : J) : ((toDiagram.obj X).obj j).hom = X.hom.app j := rfl
example {X Y : Arrow (J ⥤ C)} (a : X ⟶ Y) (j : J) :
    ((toDiagram.map a).app j).left = a.left.app j := rfl
example {X Y : Arrow (J ⥤ C)} (a : X ⟶ Y) (j : J) :
    ((toDiagram.map a).app j).right = a.right.app j := rfl
example : (equivalence J C).functor = toDiagram := rfl
example : (equivalence J C).inverse = toArrow := rfl
end Quillen.ArrowDiagrams
namespace Quillen.Waldhausen
variable {C : Type u} [Category.{v} C] (W : Structure C)
namespace ExtensionCategory
example (X : Obj (waldhausenStructure W)) :
    ((transpose W).obj X).obj.left.obj.hom = X.obj.hom.hom.left := rfl
example (X : Obj (waldhausenStructure W)) :
    ((transpose W).obj X).obj.hom.hom.left = X.obj.left.obj.hom := rfl
example {X Y : Obj (waldhausenStructure W)} (f : X ⟶ Y) :
    ((transpose W).map f).hom.left.hom.left = f.hom.left.hom.left := rfl
example {X Y : Obj (waldhausenStructure W)} (f : X ⟶ Y) :
    ((transpose W).map f).hom.left.hom.right = f.hom.right.hom.left := rfl
example {X Y : Obj (waldhausenStructure W)} {f : X ⟶ Y}
    (hf : cof (waldhausenStructure W) f) : cof (waldhausenStructure W) ((transpose W).map f) :=
  transpose_cof W hf
example : transpose W ⋙ transpose W = 𝟭 _ := transpose_transpose W
example : IsExact (waldhausenStructure (waldhausenStructure W)).cof
    (waldhausenStructure (waldhausenStructure W)).weq
    (waldhausenStructure (waldhausenStructure W)).cof
    (waldhausenStructure (waldhausenStructure W)).weq (transpose W) := transpose_exact W
end ExtensionCategory
namespace QuotientRows
variable (n : SimplexCategory)
example : (pointwiseArrowEquivalence W n).functor = arrowToRows W n := rfl
example : (pointwiseArrowEquivalence W n).inverse = rowsToArrow W n := rfl
example (X : Arrow (Obj W n)) (p : Interval n) :
    (((arrowToRows W n).obj X).obj.obj p).hom = X.hom.hom.app p := rfl
example {X Y : Arrow (Obj W n)} (f : X ⟶ Y) (p : Interval n) :
    (((arrowToRows W n).map f).hom.app p).left = f.left.hom.app p := rfl
example : IsExact (ArrowCategory.waldhausenStructure (waldhausenStructure W n)).cof
    (ArrowCategory.waldhausenStructure (waldhausenStructure W n)).weq
    (waldhausenStructure (ArrowCategory.waldhausenStructure W) n).cof
    (waldhausenStructure (ArrowCategory.waldhausenStructure W) n).weq (arrowToRows W n) :=
  arrowToRows_exact W n
example : IsExact (waldhausenStructure (ArrowCategory.waldhausenStructure W) n).cof
    (waldhausenStructure (ArrowCategory.waldhausenStructure W) n).weq
    (ArrowCategory.waldhausenStructure (waldhausenStructure W n)).cof
    (ArrowCategory.waldhausenStructure (waldhausenStructure W n)).weq (rowsToArrow W n) :=
  rowsToArrow_exact W n
example : (reedyArrowEquivalence W n).functor = reedyToRows W n := rfl
example : (reedyArrowEquivalence W n).inverse = rowsToReedy W n := rfl
example (X : ExtensionCategory.Obj (waldhausenStructure W n)) (p : Interval n) :
    (((reedyToRows W n).obj X).obj.obj p).obj.hom = X.obj.hom.hom.app p := rfl
example {X Y : ExtensionCategory.Obj (waldhausenStructure W n)} (f : X ⟶ Y) (p : Interval n) :
    (((reedyToRows W n).map f).hom.app p).hom.left = f.hom.left.hom.app p := rfl
example {X Y : Obj (ExtensionCategory.waldhausenStructure W) n} (f : X ⟶ Y) (p : Interval n) :
    ((rowsToReedy W n).map f).hom.left.hom.app p = (f.hom.app p).hom.left := rfl
example : IsExact (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).cof
    (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).weq
    (waldhausenStructure (ExtensionCategory.waldhausenStructure W) n).cof
    (waldhausenStructure (ExtensionCategory.waldhausenStructure W) n).weq (reedyToRows W n) :=
  reedyToRows_exact W n
example : IsExact (waldhausenStructure (ExtensionCategory.waldhausenStructure W) n).cof
    (waldhausenStructure (ExtensionCategory.waldhausenStructure W) n).weq
    (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).cof
    (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).weq (rowsToReedy W n) :=
  rowsToReedy_exact W n
example {m : SimplexCategory} (α : m ⟶ n) :
    (reindex W α).mapArrow ⋙ arrowToRows W m =
      arrowToRows W n ⋙ reindex (ArrowCategory.waldhausenStructure W) α := arrowToRows_reindex W α
example {m : SimplexCategory} (α : m ⟶ n) :
    rowsToReedy W n ⋙ ExtensionCategory.postcompose _ _ (reindex_exact W α) =
      reindex (ExtensionCategory.waldhausenStructure W) α ⋙ rowsToReedy W m := rowsToReedy_reindex W α
end QuotientRows
end Quillen.Waldhausen
namespace Quillen.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) {J : Arrow C ⥤ ExtensionCategory.Obj W}
  (hJ : IsExact (ArrowCategory.waldhausenStructure V).cof (ArrowCategory.waldhausenStructure V).weq
    (ExtensionCategory.waldhausenStructure W).cof (ExtensionCategory.waldhausenStructure W).weq J)
  (n : SimplexCategory)
example : IsExact (ArrowCategory.waldhausenStructure (waldhausenStructure V n)).cof
    (ArrowCategory.waldhausenStructure (waldhausenStructure V n)).weq
    (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).cof
    (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).weq (jointOnRows V W hJ n) :=
  jointOnRows_exact V W hJ n
example (X : Arrow (Obj V n)) (p : Interval n) :
    ((jointOnRows V W hJ n).obj X).obj.hom.hom.app p =
      (J.obj (Arrow.mk (X.hom.hom.app p))).obj.hom := rfl
example {X Y : Arrow (Obj V n)} (f : X ⟶ Y) (p : Interval n) :
    ((jointOnRows V W hJ n).map f).hom.right.hom.app p =
      (J.map (((arrowDiagram V n).map f).app p)).hom.right := rfl
example {m : SimplexCategory} (α : m ⟶ n) :
    (reindex V α).mapArrow ⋙ jointOnRows V W hJ m =
      jointOnRows V W hJ n ⋙ ExtensionCategory.postcompose _ _ (reindex_exact W α) :=
  jointOnRows_reindex V W hJ α
end Quillen.Waldhausen.QuotientRows
namespace Quillen.Waldhausen.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ)) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P] [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (CochainComplex.mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧)) (n : SimplexCategory)
example : IsExact
    (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure (complexSubcategory P) n)).cof
    (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure (complexSubcategory P) n)).weq
    (ExtensionCategory.waldhausenStructure (QuotientRows.waldhausenStructure (complexSubcategory P) n)).cof
    (ExtensionCategory.waldhausenStructure (QuotientRows.waldhausenStructure (complexSubcategory P) n)).weq
    (QuotientRows.jointOnRows (complexSubcategory P) (complexSubcategory P)
      (subcategoryJointFunctor_quasiExact P hcone hshift) n) :=
  QuotientRows.jointOnRows_exact _ _ (subcategoryJointFunctor_quasiExact P hcone hshift) n
example :
    let W := ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)
    IsExact (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure W n)).cof
      (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure W n)).weq
      (ExtensionCategory.waldhausenStructure (QuotientRows.waldhausenStructure W n)).cof
      (ExtensionCategory.waldhausenStructure (QuotientRows.waldhausenStructure W n)).weq
      (QuotientRows.jointOnRows W W (subcategoryJointFunctor_isoExact P hcone hshift) n) :=
  QuotientRows.jointOnRows_exact _ _ (subcategoryJointFunctor_isoExact P hcone hshift) n
end Quillen.Waldhausen.SplitFactorization
