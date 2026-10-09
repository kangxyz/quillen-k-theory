import Quillen.Waldhausen.SConstruction.WeakGridBasedHomotopy
import Quillen.Waldhausen.SConstruction.WeakNaturalTransformationBased
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let origins := #[`Quillen.Waldhausen.SConstruction.NerveCylinderZero,
    `Quillen.Waldhausen.SConstruction.WeakGridBasedHomotopy,
    `Quillen.Waldhausen.SConstruction.WeakNaturalTransformation,
    `Quillen.Waldhausen.SConstruction.WeakNaturalTransformationBased]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless origins.contains env.header.moduleNames[index.toNat]! do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 22 do throwError "Expected frozen 22-declaration scope; audited {count}"
  logInfo m!"Audited all {count} chosen-zero companion declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
open Quillen Quillen.Waldhausen
universe u v

section ZeroCylinder
variable {D : Type u} [Category.{v} D] {n m : SimplexCategory}
  {A B : Grid₂ n m ⥤ D} (η : A ⟶ B) (Z : D) (hZ : IsZero Z)
  (hA : ∀ p, A.obj p = Z) (hB : ∀ p, B.obj p = Z)
example (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram η τ = (Functor.const (Grid₂ n m)).obj Z :=
  nerveCylinderDiagram_eq_const_of_zero η Z hZ hA hB τ
end ZeroCylinder

section ExactFunctors
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))
  (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)
example : SSet.Homotopy (sSetMap hF) (sSetMap hG) :=
  weakNaturalTransformationHomotopy V W hF hG η hη
example : (deloopingMap hF).hom.Homotopy (deloopingMap hG).hom :=
  weakNaturalTransformationRealizationHomotopy V W hF hG η hη
example : (deloopingMap hF).hom.HomotopyRel (deloopingMap hG).hom {V.kBasepoint} :=
  weakNaturalTransformationBasedHomotopy V W hF hG η hη hF0 hG0
example (t : unitInterval) :
    weakNaturalTransformationRealizationHomotopy V W hF hG η hη (t, V.kBasepoint) =
      W.kBasepoint :=
  weakNaturalTransformationRealizationHomotopy_fixed_zero V W hF hG η hη hF0 hG0 t
example (n : SimplexCategoryᵒᵖ) (z : (sSet V.cof V.weq ⊗ Δ[1]).obj n) :
    ((weakNaturalTransformationHomotopy V W hF hG η hη).h.app n z).1 =
      nerveCylinderDiagram (whiskerLeft z.1.1 η) z.2.down := rfl
end ExactFunctors

section FixedFamily
variable {D : Type u} [Category.{v} D] (W : Structure D)
  {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f g : X ⟶ bisimplicialSSet W)
  (η : ∀ n m (x : (X.obj n).obj m), (((f.app n).app m) x).1 ⟶ (((g.app n).app m) x).1)
  (hη : ∀ n m x p, W.weq ((η n m x).app p))
  (hcompat : ∀ {n n'} (α : n ⟶ n') (x : (TheoremA.diagonalSSet X).obj n)
    (p : Grid₂ n'.unop n'.unop),
    HEq ((η n' n' ((TheoremA.diagonalSSet X).map α x)).app p)
      ((η n n x).app ((gridMap₂ α.unop α.unop).obj p)))
  (x : (TheoremA.diagonalSSet X) _⦋0⦌)
  (hf : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((f.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)
  (hg : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((g.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)
example (t : unitInterval) :
    diagonalWeakGridRealizationHomotopy W f g η hη hcompat (t, realizationPoint x) =
      realizationPoint (diagonalZeroVertex W) :=
  diagonalWeakGridRealizationHomotopy_fixed_vertex W f g η hη hcompat x hf hg t
end FixedFamily
