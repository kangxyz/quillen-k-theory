import Quillen.Waldhausen.Fibration.Rows.ExtensionAxiom
import Quillen.Waldhausen.Fibration.ComplexChainReplacement
import Quillen.Waldhausen.Fibration.ComplexExtension
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.Rows.ExtensionAxiom]
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
  unless count == 2 do
    throwError "Expected fixed 2 coarse-row-extension origins, found {count}"
  logInfo m!"Audited all {count} coarse-row-extension declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration
section Generic
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse) (n : SimplexCategory)
example : ExtensionAxiom (RowWeakEquivalences.coarseStructure N n) := RowWeakEquivalences.extensionAxiom N he n
example : ExtensionAxiom (RowWeakEquivalences.nested N n).coarse := RowWeakEquivalences.extensionAxiom N he n
example : ExtensionAxiom (RowWeakEquivalences.coarseStructure N ⦋0⦌) := RowWeakEquivalences.extensionAxiom N he ⦋0⦌
example {A B Q : QuotientRows.Obj V n} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : QuotientRows.cof V n i)
    (h : IsPushout i ((RowWeakEquivalences.coarseStructure N n).isZero.from_ A)
      q ((RowWeakEquivalences.coarseStructure N n).isZero.to_ Q)) (p : Interval n) :
    IsPushout (i.hom.app p) (N.coarse.isZero.from_ (A.obj.obj p))
      (q.hom.app p) (N.coarse.isZero.to_ (Q.obj.obj p)) :=
  RowWeakEquivalences.cofiber_evaluation_isPushout N hi h p
example {A B Q A' B' Q' : QuotientRows.Obj V n}
    {i : A ⟶ B} {q : B ⟶ Q} {i' : A' ⟶ B'} {q' : B' ⟶ Q'}
    (hi : QuotientRows.cof V n i) (hi' : QuotientRows.cof V n i')
    (h : IsPushout i ((RowWeakEquivalences.coarseStructure N n).isZero.from_ A)
      q ((RowWeakEquivalences.coarseStructure N n).isZero.to_ Q))
    (h' : IsPushout i' ((RowWeakEquivalences.coarseStructure N n).isZero.from_ A')
      q' ((RowWeakEquivalences.coarseStructure N n).isZero.to_ Q'))
    (a : A ⟶ A') (b : B ⟶ B') (c : Q ⟶ Q')
    (wi : i ≫ b = a ≫ i') (wq : q ≫ c = b ≫ q')
    (ha : ∀ p, N.coarse.weq (a.hom.app p)) (hc : ∀ p, N.coarse.weq (c.hom.app p)) :
    ∀ p, N.coarse.weq (b.hom.app p) :=
  (RowWeakEquivalences.extensionAxiom N he n).extension hi hi' h h' a b c wi wq ha hc
example (m : SimplexCategory) : ExtensionAxiom
    (RowWeakEquivalences.coarseStructure (RowWeakEquivalences.nested N n) m) :=
  RowWeakEquivalences.extensionAxiom (RowWeakEquivalences.nested N n)
    (RowWeakEquivalences.extensionAxiom N he n) m
example {A B Q : QuotientRows.Obj V n} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : QuotientRows.cof V n i)
    (h : IsPushout i ((RowWeakEquivalences.coarseStructure N n).isZero.from_ A)
      q ((RowWeakEquivalences.coarseStructure N n).isZero.to_ Q)) :
    (RowWeakEquivalences.coarseStructure N n).weq i ↔
      Acyclic (RowWeakEquivalences.coarseStructure N n) Q :=
  weak_iff_acyclic_of_isPushout _ (RowWeakEquivalences.extensionAxiom N he n) hi h
end Generic
section Complexes
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
example (n : SimplexCategory) : ExtensionAxiom
    (RowWeakEquivalences.coarseStructure (complexSubcategoryNested P) n) :=
  RowWeakEquivalences.extensionAxiom _ (complexSubcategory_extensionAxiom P) n
end Complexes
section BoundedAndScheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example (n : SimplexCategory) : ExtensionAxiom
    (RowWeakEquivalences.coarseStructure (boundedTermsNested P) n) :=
  RowWeakEquivalences.extensionAxiom _ (complexSubcategory_extensionAxiom (boundedTerms P)) n
example (X : Scheme.{u}) (n : SimplexCategory) : ExtensionAxiom
    (RowWeakEquivalences.coarseStructure (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) n) :=
  RowWeakEquivalences.extensionAxiom _ (complexSubcategory_extensionAxiom _) n
end BoundedAndScheme
end Quillen.Waldhausen.Fibration
