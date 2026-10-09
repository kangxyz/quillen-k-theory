import Quillen.Waldhausen.ExtensionCategory.Cofiber
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.ExtensionCategory.Basic,
    `Quillen.Waldhausen.ExtensionCategory.PushoutCube,
    `Quillen.Waldhausen.ExtensionCategory.RelativeCofibrations,
    `Quillen.Waldhausen.ExtensionCategory.ArrowPushouts,
    `Quillen.Waldhausen.ExtensionCategory.Structure,
    `Quillen.Waldhausen.ExtensionCategory.Cofiber]
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
  unless count == 64 do throwError "Expected 64 extension-category origins, got {count}"
  logInfo m!"Audited all {count} extension-category declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Waldhausen.Structure C)
example : Type (max u v) := Obj W
example : Category.{v} (Obj W) := inferInstance
example : Waldhausen.Structure (Obj W) := waldhausenStructure W
example (X : Obj W) : W.cof X.obj.hom := X.property
example {X Y : Obj W} (f : X ⟶ Y) :
    (waldhausenStructure W).cof f ↔ W.cof f.hom.left ∧ W.cof (relativeMap W f) := Iff.rfl
example {X Y : Obj W} (f : X ⟶ Y) :
    (waldhausenStructure W).weq f ↔ W.weq f.hom.left ∧ W.weq f.hom.right := Iff.rfl
example {A B D P : Obj W} {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ P} {j : D ⟶ P}
    (hf : cof W f) (h : IsPushout f g i j) :
    IsPushout f.hom.left g.hom.left i.hom.left j.hom.left ∧
      IsPushout f.hom.right g.hom.right i.hom.right j.hom.right := pointwise_of_isPushout W hf h
example : IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq W.cof W.weq (source W) := source_exact W
example : IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq W.cof W.weq (middle W) := middle_exact W
example : IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq W.cof W.weq (cofiber W) := cofiber_exact W
example (X : Obj W) : (inclusion W).app X = X.obj.hom := rfl
example (X : Obj W) : (quotient W).app X =
    Additivity.sourceι W (inclusion W) (inclusion_cof W) (Arrow.mk (toZero W X)) := rfl
example (X : Obj W) : IsPushout X.obj.hom (W.isZero.from_ X.obj.left)
    ((quotient W).app X) (W.isZero.to_ ((cofiber W).obj X)) := cofiber_isPushout W X
example : Additivity.IsCofibrationSequence (waldhausenStructure W) W (inclusion W) (quotient W) :=
  isCofibrationSequence W
end Quillen.Waldhausen.ExtensionCategory

namespace Quillen.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Waldhausen.Structure C)
example : (waldhausenStructure W).zero = ⟨Arrow.mk (𝟙 W.zero), W.cof.id_mem _⟩ := rfl
example {X Y : Obj W} (f : X ⟶ Y) : (source W).map f = f.hom.left := rfl
example {X Y : Obj W} (f : X ⟶ Y) : (middle W).map f = f.hom.right := rfl
example {X Y : Obj W} (f : X ⟶ Y)
    {R : C} {i : X.obj.right ⟶ R} {j : Y.obj.left ⟶ R}
    (h : IsPushout X.obj.hom f.hom.left i j) (k : R ⟶ Y.obj.right)
    (hi : i ≫ k = f.hom.right) (hj : j ≫ k = Y.obj.hom) :
    cof W f ↔ W.cof f.hom.left ∧ W.cof k := by
  constructor
  · intro hf
    exact ⟨hf.1, cof_relative W hf h k hi hj⟩
  · rintro ⟨hf, hk⟩
    exact cof_of_relative W f hf h k hi hj hk
example {X Y Z : Obj W} (f : X ⟶ Y) (g : X ⟶ Z) (hf : cof W f) :
    ∃ (P : Obj W) (i : Y ⟶ P) (j : Z ⟶ P), IsPushout f g i j ∧
      IsPushout f.hom.left g.hom.left i.hom.left j.hom.left ∧
      IsPushout f.hom.right g.hom.right i.hom.right j.hom.right ∧ cof W j :=
  exists_pointwise_pushout W f g hf
example {X Y : Obj W} (f : X ⟶ Y) :
    (cofiber W).map f = (relativeFunctor W).map ((terminalArrow W).map f) := rfl
example (X : Obj W) :
    (cofiber W).obj X = (relativeFunctor W).obj (Arrow.mk (toZero W X)) := rfl
end Quillen.Waldhausen.ExtensionCategory
