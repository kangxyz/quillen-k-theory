import Quillen.Waldhausen.ExtensionCategory.Realization
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.ExtensionCategory.Product,
    `Quillen.Waldhausen.ExtensionCategory.ExactTransport,
    `Quillen.Waldhausen.ExtensionCategory.Split,
    `Quillen.Waldhausen.ExtensionCategory.SplitQuotient,
    `Quillen.Waldhausen.ExtensionCategory.Realization]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 81 do throwError "Expected 81 extension-realization origins, got {count}"
  logInfo m!"Audited all {count} extension-realization declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.ExtensionCategory
section Algebra
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (V : Structure C) (W : Structure D)
example : (productStructure V W).zero = (V.zero, W.zero) := rfl
example {X Y : C × D} (f : X ⟶ Y) :
    (productStructure V W).cof f ↔ V.cof f.1 ∧ W.cof f.2 := Iff.rfl
example {X Y : C × D} (f : X ⟶ Y) :
    (productStructure V W).weq f ↔ V.weq f.1 ∧ W.weq f.2 := Iff.rfl
example {F G : C ⥤ D} (hF : IsExact V.cof V.weq W.cof W.weq F) (e : F ≅ G) :
    IsExact V.cof V.weq W.cof W.weq G := isExact_of_natIso V W hF e
example (X : Obj V) : (sourceCofiber V).obj X = (X.obj.left, (cofiber V).obj X) := rfl
example : IsExact (waldhausenStructure V).cof (waldhausenStructure V).weq
    (productStructure V V).cof (productStructure V V).weq (sourceCofiber V) := sourceCofiber_exact V
variable [HasBinaryCoproducts C] [HasBinaryCoproducts (Obj V)]
example (X : C × C) : ((split V).obj X).obj.hom = (coprod.inr : X.1 ⟶ X.2 ⨿ X.1) := rfl
example {X Y : C × C} (f : X ⟶ Y) : ((split V).map f).hom.left = f.1 := rfl
example {X Y : C × C} (f : X ⟶ Y) : ((split V).map f).hom.right = coprod.map f.2 f.1 := rfl
example : IsExact (productStructure V V).cof (productStructure V V).weq
    (waldhausenStructure V).cof (waldhausenStructure V).weq (split V) := split_exact V
example (X : C × C) : (quotient V).app ((split V).obj X) ≫ (splitCofiberIso V X).hom =
    (splitProjection V).app X := quotient_splitCofiberIso V X
example : split V ⋙ sourceCofiber V ≅ 𝟭 (C × C) := splitSourceCofiberIso V
example : Additivity.sumFunctor (cofiber V ⋙ zeroEmbedding V) (source V ⋙ identityEmbedding V) ≅
    sourceCofiber V ⋙ split V := internalSumSplitIso V
end Algebra
section Realization
variable {C : Type u} [Category.{u} C] (W : Structure C)
example : ContinuousMap.HomotopyEquiv (waldhausenStructure W).Delooping
    (productStructure W W).Delooping := realizationHomotopyEquiv W
example : (realizationHomotopyEquiv W).toFun = (deloopingMap (sourceCofiber_exact W)).hom := rfl
example : (realizationHomotopyEquiv W).invFun = splitRealizationMap W := rfl
example (x : (waldhausenStructure W).Delooping) :
    realizationHomotopyEquiv W x = deloopingMap (sourceCofiber_exact W) x := rfl
end Realization
end Quillen.Waldhausen.ExtensionCategory
