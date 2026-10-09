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
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 32 do throwError "Expected 32 joint-source origins, got {count}"
  logInfo m!"Audited all {count} actual joint-source origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.SplitFactorization
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]

-- Original object and morphism formulas, with no cone, shift or kernel closure.
example (f : Arrow P.FullSubcategory) :
    (subcategoryJointSourceFunctor P).obj f = subcategoryJointSource P f := rfl
example (f : Arrow P.FullSubcategory) :
    ((subcategoryJointSourceFunctor P).obj f).obj = (f.left.obj ⊞ f.right.obj) := rfl
example {f g : Arrow P.FullSubcategory} (α : f ⟶ g) :
    ((subcategoryJointSourceFunctor P).map α).hom = biprod.map α.left.hom α.right.hom := rfl
example (f : Arrow P.FullSubcategory) :
    IsColimit (BinaryCofan.mk ((subcategoryJointSourceInl P).app f)
      ((subcategoryJointSourceInr P).app f)) := subcategoryJointSourceCofanIsColimit P f

variable [P.IsClosedUnderFiniteProducts]
example (W : Structure P.FullSubcategory) :
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      W.cof W.weq (subcategoryJointSourceFunctor P) := subcategoryJointSourceFunctor_isExact P W
example (W : Structure P.FullSubcategory) {f : Arrow P.FullSubcategory} (hf : IsZero f) :
    IsZero ((subcategoryJointSourceFunctor P).obj f) :=
  (subcategoryJointSourceFunctor_isExact P W).zero hf
example (W : Structure P.FullSubcategory) {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
    (hL : W.cof α.left) (hR : W.cof α.right) : W.cof ((subcategoryJointSourceFunctor P).map α) :=
  (subcategoryJointSourceFunctor_isExact P W).cofibration α ⟨hL, hR⟩
example (W : Structure P.FullSubcategory) {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
    (hL : W.weq α.left) (hR : W.weq α.right) : W.weq ((subcategoryJointSourceFunctor P).map α) :=
  (subcategoryJointSourceFunctor_isExact P W).weak α ⟨hL, hR⟩
example (W : Structure P.FullSubcategory) {F G H T : Arrow P.FullSubcategory}
    {f : F ⟶ G} {g : F ⟶ H} {i : G ⟶ T} {j : H ⟶ T}
    (hf : W.cof f.left ∧ W.cof f.right)
    (hL : IsPushout f.left g.left i.left j.left) (hR : IsPushout f.right g.right i.right j.right) :
    IsPushout ((subcategoryJointSourceFunctor P).map f) ((subcategoryJointSourceFunctor P).map g)
      ((subcategoryJointSourceFunctor P).map i) ((subcategoryJointSourceFunctor P).map j) :=
  subcategoryJointSourceFunctor_map_isPushout P W hf hL hR

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
example :
    let W := ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      W.cof W.weq (subcategoryJointSourceFunctor P) := subcategoryJointSourceFunctor_isoExact P
example :
    IsExact (ArrowCategory.waldhausenStructure (complexSubcategory P)).cof
      (ArrowCategory.waldhausenStructure (complexSubcategory P)).weq
      (complexSubcategory P).cof (complexSubcategory P).weq (subcategoryJointSourceFunctor P) :=
  subcategoryJointSourceFunctor_quasiExact P
example {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
    (hL : subcategoryCofibrations P α.left) (hR : subcategoryCofibrations P α.right) :
    subcategoryCofibrations P ((subcategoryJointSourceFunctor P).map α) :=
  (subcategoryJointSourceFunctor_quasiExact P).cofibration α ⟨hL, hR⟩
example {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
    (hL : QuasiIso α.left.hom) (hR : QuasiIso α.right.hom) :
    QuasiIso (biprod.map α.left.hom α.right.hom) :=
  (subcategoryJointSourceFunctor_quasiExact P).weak α ⟨hL, hR⟩
