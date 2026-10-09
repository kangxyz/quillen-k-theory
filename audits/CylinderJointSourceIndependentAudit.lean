import Quillen.Waldhausen.Cylinder.JointSource
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Waldhausen.Cylinder.JointSource
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 32 do throwError "Expected 32 original joint-source origins, got {count}"
  logInfo m!"Audited all {count} joint-source origins."
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen SplitFactorization
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
-- No cone or shift closure is needed, and W can be any genuine structure.
example (W : Structure P.FullSubcategory) :
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      W.cof W.weq (subcategoryJointSourceFunctor P) :=
  subcategoryJointSourceFunctor_isExact P W
example (f : Arrow P.FullSubcategory) :
    ((subcategoryJointSourceFunctor P).obj f).obj = (f.left.obj ⊞ f.right.obj) := rfl
example {f g : Arrow P.FullSubcategory} (α : f ⟶ g) :
    ((subcategoryJointSourceFunctor P).map α).hom = biprod.map α.left.hom α.right.hom := rfl
example (W : Structure P.FullSubcategory)
    {F G H T : Arrow P.FullSubcategory} {f : F ⟶ G} {g : F ⟶ H} {i : G ⟶ T} {j : H ⟶ T}
    (hf : W.cof f.left ∧ W.cof f.right)
    (hL : IsPushout f.left g.left i.left j.left) (hR : IsPushout f.right g.right i.right j.right) :
    IsPushout ((subcategoryJointSourceFunctor P).map f) ((subcategoryJointSourceFunctor P).map g)
      ((subcategoryJointSourceFunctor P).map i) ((subcategoryJointSourceFunctor P).map j) :=
  subcategoryJointSourceFunctor_map_isPushout P W hf hL hR
