import Quillen.Waldhausen.Fibration.RelativeRows.WeakInterchange
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.SConstruction.Rows.Interchange,
    `Quillen.Waldhausen.Fibration.RelativeRows.Interchange,
    `Quillen.Waldhausen.Fibration.RelativeRows.WeakInterchange]
  let mut counts : Array Nat := #[0,0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (·+1)
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless counts == #[26,28,24] do throwError "Expected78 origins (26+28+24), got {counts}"
  logInfo m!"Audited all78 interchange origins: {counts}"
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Generic
variable {C : Type u} [Category.{v} C] (W : Structure C) (N : NestedWeakEquivalences W)
  (m n : SimplexCategory)
example : QuotientRows.Obj (QuotientRows.waldhausenStructure W n) m ≌
    QuotientRows.Obj (QuotientRows.waldhausenStructure W m) n := QuotientRows.rowInterchange W m n
example (X : QuotientRows.Obj (QuotientRows.waldhausenStructure W n) m)
    (p : Interval n) (q : Interval m) :
    (((QuotientRows.transposeRows W m n).obj X).obj.obj p).obj.obj q =
      (X.obj.obj q).obj.obj p := rfl
example {X Y : QuotientRows.Obj (QuotientRows.waldhausenStructure W n) m} (f : X ⟶ Y)
    (p : Interval n) (q : Interval m) :
    (((QuotientRows.transposeRows W m n).map f).hom.app p).hom.app q =
      (f.hom.app q).hom.app p := rfl
example {X Y : QuotientRows.Obj (QuotientRows.waldhausenStructure W n) m} (f : X ⟶ Y)
    (hf : QuotientRows.cof (QuotientRows.waldhausenStructure W n) m f) :
    QuotientRows.cof (QuotientRows.waldhausenStructure W m) n ((QuotientRows.transposeRows W m n).map f) :=
  QuotientRows.transposeRows_cof W hf
example : IsExact (QuotientRows.waldhausenStructure (QuotientRows.waldhausenStructure W n) m).cof
    (QuotientRows.waldhausenStructure (QuotientRows.waldhausenStructure W n) m).weq
    (QuotientRows.waldhausenStructure (QuotientRows.waldhausenStructure W m) n).cof
    (QuotientRows.waldhausenStructure (QuotientRows.waldhausenStructure W m) n).weq
    (QuotientRows.transposeRows W m n) := QuotientRows.transposeRows_exact W m n
example {m' : SimplexCategory} (α : m' ⟶ m) :
    QuotientRows.reindex (QuotientRows.waldhausenStructure W n) α ⋙ QuotientRows.transposeRows W m' n =
      QuotientRows.transposeRows W m n ⋙ QuotientRows.postcompose (QuotientRows.waldhausenStructure W m)
        (QuotientRows.waldhausenStructure W m') (QuotientRows.reindex_exact W α) n :=
  QuotientRows.transposeRows_reindex_outer W α
example (X : QuotientRows.Obj W m) :
    Acyclic (RowWeakEquivalences.coarseStructure N m) X ↔ ∀ p, Acyclic N.coarse (X.obj.obj p) :=
  rowAcyclic_iff N X
example : QuotientRows.Obj (RelativeRows.waldhausenStructure N n) m ≌
    RelativeRows.Obj (RowWeakEquivalences.nested N m) n := RelativeRows.innerSEquivalence N m n
example : RelativeRows.innerSInterchange N m n ⋙ RelativeRows.innerSInverse N m n = 𝟭 _ :=
  RelativeRows.innerSInterchange_inverse N m n
example : RelativeRows.innerSInverse N m n ⋙ RelativeRows.innerSInterchange N m n = 𝟭 _ :=
  RelativeRows.innerSInverse_interchange N m n
example : IsExact (QuotientRows.waldhausenStructure (RelativeRows.waldhausenStructure N n) m).cof
    (QuotientRows.waldhausenStructure (RelativeRows.waldhausenStructure N n) m).weq
    (RelativeRows.waldhausenStructure (RowWeakEquivalences.nested N m) n).cof
    (RelativeRows.waldhausenStructure (RowWeakEquivalences.nested N m) n).weq
    (RelativeRows.innerSInterchange N m n) := RelativeRows.innerSInterchange_exact N m n
example : IsExact (RelativeRows.waldhausenStructure (RowWeakEquivalences.nested N m) n).cof
    (RelativeRows.waldhausenStructure (RowWeakEquivalences.nested N m) n).weq
    (QuotientRows.waldhausenStructure (RelativeRows.waldhausenStructure N n) m).cof
    (QuotientRows.waldhausenStructure (RelativeRows.waldhausenStructure N n) m).weq
    (RelativeRows.innerSInverse N m n) := RelativeRows.innerSInverse_exact N m n
example {n' : SimplexCategory} (α : n' ⟶ n) :
    QuotientRows.postcompose (RelativeRows.waldhausenStructure N n) (RelativeRows.waldhausenStructure N n')
      (RelativeRows.reindex_exact N α) m ⋙ RelativeRows.innerSInterchange N m n' =
      RelativeRows.innerSInterchange N m n ⋙ RelativeRows.reindex (RowWeakEquivalences.nested N m) α :=
  RelativeRows.innerSInterchange_reindex N α
example : RelativeRows.InnerSWeakRows N m n ≌ RelativeRows.RelativeInnerSWeakRows N m n :=
  RelativeRows.innerSWeakEquivalence N m n
example : (RelativeRows.innerSWeakClassifyingHomotopyEquiv N m n).toFun =
    (classifyingSpaceMap (RelativeRows.innerSWeakInterchange N m n)).hom := rfl
example : (RelativeRows.innerSWeakClassifyingHomotopyEquiv N m n).invFun =
    (classifyingSpaceMap (RelativeRows.innerSWeakInverse N m n)).hom := rfl
example {X Y : RelativeRows.InnerSWeakRows N m n} (f : X ⟶ Y)
    (p : Interval (RelativeRows.addInitial.obj n)) (q : Interval m) :
    (((RelativeRows.innerSWeakInterchange N m n).map f).hom.hom.hom.app p).hom.app q =
      ((f.hom.hom.app q).hom.hom.app p) := rfl
example : RelativeRows.InnerSWeakRows N ⦋0⦌ ⦋0⦌ ≌ RelativeRows.RelativeInnerSWeakRows N ⦋0⦌ ⦋0⦌ :=
  RelativeRows.innerSWeakEquivalence N ⦋0⦌ ⦋0⦌
end Generic
section Schemes
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
example (X : Scheme.{u}) (m n : SimplexCategory) :
    RelativeRows.InnerSWeakRows (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) m n ≌
      RelativeRows.RelativeInnerSWeakRows (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) m n :=
  RelativeRows.innerSWeakEquivalence _ _ _
end Schemes

/- Independent strengthening: exact literal components in both directions,
   both original ordinal restrictions, genuine Reedy reflection and zero. -/
section Independent
variable {C : Type u} [Category.{v} C] (W : Structure C) (N : NestedWeakEquivalences W)
  (m n : SimplexCategory)
example {n' : SimplexCategory} (α : n' ⟶ n) :
    QuotientRows.postcompose (QuotientRows.waldhausenStructure W n)
      (QuotientRows.waldhausenStructure W n') (QuotientRows.reindex_exact W α) m ⋙
      QuotientRows.transposeRows W m n' =
    QuotientRows.transposeRows W m n ⋙ QuotientRows.reindex (QuotientRows.waldhausenStructure W m) α :=
  QuotientRows.transposeRows_reindex_inner W α
example {X Y : RelativeRows.Obj (RowWeakEquivalences.nested N m) n} (f : X ⟶ Y)
    (hf : (RelativeRows.waldhausenStructure (RowWeakEquivalences.nested N m) n).cof f) :
    (QuotientRows.waldhausenStructure (RelativeRows.waldhausenStructure N n) m).cof
      ((RelativeRows.innerSInverse N m n).map f) := RelativeRows.innerSInverse_cof N f hf
example (X : QuotientRows.Obj (RelativeRows.waldhausenStructure N n) m)
    (p : Interval (RelativeRows.addInitial.obj n)) (q : Interval m) :
    ((((RelativeRows.innerSInterchange N m n).obj X).obj.obj.obj p).obj.obj q) =
      (X.obj.obj q).obj.obj.obj p := rfl
example (X : RelativeRows.Obj (RowWeakEquivalences.nested N m) n)
    (p : Interval (RelativeRows.addInitial.obj n)) (q : Interval m) :
    ((((RelativeRows.innerSInverse N m n).obj X).obj.obj q).obj.obj.obj p) =
      (X.obj.obj.obj p).obj.obj q := rfl
example {X Y : RelativeRows.RelativeInnerSWeakRows N m n} (f : X ⟶ Y)
    (p : Interval (RelativeRows.addInitial.obj n)) (q : Interval m) :
    ((((RelativeRows.innerSWeakInverse N m n).map f).hom.hom.app q).hom.hom.app p) =
      (f.hom.hom.hom.app p).hom.app q := rfl
example : IsZero ((RelativeRows.innerSInterchange N m n).obj
    (QuotientRows.waldhausenStructure (RelativeRows.waldhausenStructure N n) m).zero) :=
  (RelativeRows.innerSInterchange_exact N m n).zero
    (QuotientRows.waldhausenStructure (RelativeRows.waldhausenStructure N n) m).isZero
example {Z : C} (hZ : IsZero Z) (X : C) :
    Acyclic N.coarse X ↔ N.coarse.weq (hZ.to_ X) := acyclic_iff_weak_from_isZero N.coarse hZ X
example : RelativeRows.innerSWeakInterchange N m n ⋙ RelativeRows.innerSWeakInverse N m n = 𝟭 _ :=
  RelativeRows.innerSWeakInterchange_inverse N m n
end Independent
