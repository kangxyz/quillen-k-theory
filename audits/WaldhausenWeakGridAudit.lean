import Quillen.Waldhausen.SConstruction.WeakGridHomotopy
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let origins := #[`Quillen.Waldhausen.SConstruction.NerveCylinder,
    `Quillen.Waldhausen.SConstruction.NerveCylinderNaturality,
    `Quillen.Waldhausen.SConstruction.WeakGridHomotopy]
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
  unless count == 26 do throwError "Expected frozen 26-declaration scope; audited {count}"
  logInfo m!"Audited all {count} genuine weak-grid declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
open Quillen Quillen.Waldhausen
universe u v
variable {D : Type u} [Category.{v} D] (W : Structure D)

section Cylinder
variable {n m : SimplexCategory} {A B : Grid₂ n m ⥤ D} (η : A ⟶ B)
  (hη : ∀ p, W.weq (η.app p)) (hA : IsSimplex₂ W.cof W.weq A)
  (hB : IsSimplex₂ W.cof W.weq B)
example (τ : m ⟶ ⦋1⦌) : IsSimplex₂ W.cof W.weq (nerveCylinderDiagram η τ) :=
  nerveCylinderDiagram_isSimplex₂ W η hη hA hB τ
example : nerveCylinderDiagram η (SimplexCategory.const m ⦋1⦌ 0) = A :=
  nerveCylinderDiagram_zero η
example : nerveCylinderDiagram η (SimplexCategory.const m ⦋1⦌ 1) = B :=
  nerveCylinderDiagram_one η
example {n' m' : SimplexCategory} (α : n' ⟶ n) (β : m' ⟶ m) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (whiskerLeft (gridMap₂ α β) η) (β ≫ τ) =
      gridMap₂ α β ⋙ nerveCylinderDiagram η τ := nerveCylinderDiagram_precomp η α β τ
end Cylinder

section Family
variable {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f g : X ⟶ bisimplicialSSet W)
  (η : ∀ n m (x : (X.obj n).obj m), (((f.app n).app m) x).1 ⟶ (((g.app n).app m) x).1)
  (hη : ∀ n m x p, W.weq ((η n m x).app p))
  (hcompat : ∀ {n n'} (α : n ⟶ n') (x : (TheoremA.diagonalSSet X).obj n)
    (p : Grid₂ n'.unop n'.unop),
    HEq ((η n' n' ((TheoremA.diagonalSSet X).map α x)).app p)
      ((η n n x).app ((gridMap₂ α.unop α.unop).obj p)))
example : SSet.Homotopy (TheoremA.diagonalMap f) (TheoremA.diagonalMap g) :=
  diagonalWeakGridHomotopy W f g η hη hcompat
example : (SSet.toTop.map (TheoremA.diagonalMap f)).hom.Homotopy
    (SSet.toTop.map (TheoremA.diagonalMap g)).hom :=
  diagonalWeakGridRealizationHomotopy W f g η hη hcompat
example (n : SimplexCategoryᵒᵖ)
    (z : (TheoremA.diagonalSSet X ⊗ Δ[1]).obj n) :
    ((diagonalWeakGridHomotopy W f g η hη hcompat).h.app n z).1 =
      nerveCylinderDiagram (η n n z.1) z.2.down := rfl
end Family
