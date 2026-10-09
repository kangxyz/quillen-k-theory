import Quillen.Waldhausen.SConstruction.Bisimplicial
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let origin := `Quillen.Waldhausen.SConstruction.Bisimplicial
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 68 do throwError "Expected frozen 68-declaration scope; audited {count}"
  logInfo m!"Audited all {count} genuine bisimplicial S-grid declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open Quillen Quillen.Waldhausen
universe u v u' v'

variable {C : Type u} [Category.{v} C] (V : Structure C)

example : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := bisimplicialSSet V
example : TheoremA.diagonalSSet (bisimplicialSSet V) ≅ sSet V.cof V.weq :=
  bisimplicialDiagonalIso V
example (n : SimplexCategoryᵒᵖ)
    (F : (TheoremA.diagonalSSet (bisimplicialSSet V)).obj n) :
    ((bisimplicialDiagonalIso V).hom.app n F).1 = F.1 := rfl
example (n : SimplexCategoryᵒᵖ) (F : (sSet V.cof V.weq).obj n) :
    ((bisimplicialDiagonalIso V).inv.app n F).1 = F.1 := rfl
example (n : SimplexCategoryᵒᵖ) :
    (bisimplicialDiagonalIso V).hom.app n
      (zeroSimplex₂ V.cof V.weq V.zero V.isZero n n) =
      zeroSimplex V.cof V.weq V.zero V.isZero n := rfl
example {n' n m' m : SimplexCategory} (α : n' ⟶ n) (β : m' ⟶ m)
    (F : Grid₂ n m ⥤ C) (hF : IsSimplex₂ V.cof V.weq F) :
    IsSimplex₂ V.cof V.weq (gridMap₂ α β ⋙ F) := hF.precomp V.cof V.weq α β
example {n' n m' m : SimplexCategory} (α : n' ⟶ n) (β : m' ⟶ m) :
    gridMap₂ α (𝟙 m') ⋙ gridMap₂ (𝟙 n) β =
      gridMap₂ (𝟙 n') β ⋙ gridMap₂ α (𝟙 m) := gridMap₂_interchange α β

section DifferentUniverses
variable {D : Type u'} [Category.{v'} D] (W : Structure D) {G : C ⥤ D}
    (hG : IsExact V.cof V.weq W.cof W.weq G)
example {n m : SimplexCategory} (F : Grid₂ n m ⥤ C) (hF : IsSimplex₂ V.cof V.weq F) :
    IsSimplex₂ W.cof W.weq (F ⋙ G) := hF.postcomp V.cof V.weq hG
end DifferentUniverses

section SameUniverses
variable {D : Type u} [Category.{v} D] (W : Structure D) {G : C ⥤ D}
    (hG : IsExact V.cof V.weq W.cof W.weq G)
example : bisimplicialSSet V ⟶ bisimplicialSSet W := bisimplicialSSetMap V.cof V.weq hG
example (n m : SimplexCategoryᵒᵖ) (F : ((bisimplicialSSet V).obj n).obj m) :
    (((bisimplicialSSetMap V.cof V.weq hG).app n).app m F).1 = F.1 ⋙ G := rfl
example :
    TheoremA.diagonalMap (bisimplicialSSetMap V.cof V.weq hG) ≫ (bisimplicialDiagonalIso W).hom =
      (bisimplicialDiagonalIso V).hom ≫ sSetMap hG :=
  bisimplicialDiagonalIso_naturality V.cof V.weq hG
end SameUniverses

#print axioms Quillen.Waldhausen.bisimplicialDiagonalIsoOfProperties
#print axioms Quillen.Waldhausen.bisimplicialDiagonalIso_naturality
#check @Quillen.Waldhausen.bisimplicialSSet
#check @Quillen.Waldhausen.IsSimplex₂.postcomp
