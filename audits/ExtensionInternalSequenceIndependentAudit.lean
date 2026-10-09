import Quillen.Waldhausen.ExtensionCategory.InternalSequence
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.ExtensionCategory.Embeddings,
    `Quillen.Waldhausen.ExtensionCategory.InternalSequence]
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
  unless count == 50 do throwError "Expected 50 internal extension-sequence origins, got {count}"
  logInfo m!"Audited all {count} internal extension-sequence declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Waldhausen.Structure C)
example (X : C) : ((identityEmbedding W).obj X).obj.hom = 𝟙 X := rfl
example (X : C) : ((zeroEmbedding W).obj X).obj.hom = W.isZero.to_ X := rfl
example : IsExact W.cof W.weq (waldhausenStructure W).cof (waldhausenStructure W).weq
    (identityEmbedding W) := identityEmbedding_exact W
example : IsExact W.cof W.weq (waldhausenStructure W).cof (waldhausenStructure W).weq
    (zeroEmbedding W) := zeroEmbedding_exact W
example (X : Obj W) : ((identityToExtension W).app X).hom.left = 𝟙 X.obj.left := rfl
example (X : Obj W) : ((identityToExtension W).app X).hom.right = X.obj.hom := rfl
example (X : Obj W) : ((extensionToZero W).app X).hom.left = W.isZero.from_ X.obj.left := rfl
example (X : Obj W) : ((extensionToZero W).app X).hom.right = (quotient W).app X := rfl
example {X Y : Obj W} (f : X ⟶ Y) : (subextensionComparison W f).hom.left = 𝟙 Y.obj.left := rfl
example {X Y : Obj W} (f : X ⟶ Y) : (subextensionComparison W f).hom.right = relativeMap W f := rfl
example {X Y : Obj W} (f : X ⟶ Y) (hf : cof W f) : cof W (subextensionComparison W f) :=
  subextensionComparison_cof W f hf
example (X : Obj W) : IsPushout ((identityToExtension W).app X)
    ((isZero W).from_ ((source W ⋙ identityEmbedding W).obj X))
    ((extensionToZero W).app X)
    ((isZero W).to_ ((cofiber W ⋙ zeroEmbedding W).obj X)) := internal_cofiber_isPushout W X
example : Additivity.IsCofibrationSequence (waldhausenStructure W) (waldhausenStructure W)
    (identityToExtension W) (extensionToZero W) := internalIsCofibrationSequence W
end Quillen.Waldhausen.ExtensionCategory

namespace Quillen.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Waldhausen.Structure C)
example {A B : C} (f : A ⟶ B) : ((identityEmbedding W).map f).hom.left = f := rfl
example {A B : C} (f : A ⟶ B) : ((identityEmbedding W).map f).hom.right = f := rfl
example {A B : C} (f : A ⟶ B) : ((zeroEmbedding W).map f).hom.left = 𝟙 W.zero := rfl
example {A B : C} (f : A ⟶ B) : ((zeroEmbedding W).map f).hom.right = f := rfl
example {X Y : Obj W} (f : X ⟶ Y) : (subextensionPushout W f).obj.left = Y.obj.left := rfl
example {X Y : Obj W} (f : X ⟶ Y) :
    (subextensionPushout W f).obj.right = (relativeFunctor W).obj (Arrow.mk f) := rfl
example {X Y : Obj W} (f : X ⟶ Y) :
    IsPushout ((identityToExtension W).app X) ((source W ⋙ identityEmbedding W).map f)
      (subextensionInl W f) (subextensionInr W f) := subextension_isPushout W f
example {X Y : Obj W} (f : X ⟶ Y) :
    subextensionInl W f ≫ subextensionComparison W f = f := subextensionInl_comparison W f
example {X Y : Obj W} (f : X ⟶ Y) :
    subextensionInr W f ≫ subextensionComparison W f = (identityToExtension W).app Y :=
  subextensionInr_comparison W f
example : Additivity.IsCofibrationTransformation (waldhausenStructure W)
    (identityToExtension W) (waldhausenStructure W) :=
  identityToExtension_isCofibrationTransformation W
example : IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq
    (waldhausenStructure W).cof (waldhausenStructure W).weq
    (source W ⋙ identityEmbedding W) := (internalIsCofibrationSequence W).exactF
example : IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq
    (waldhausenStructure W).cof (waldhausenStructure W).weq
    (cofiber W ⋙ zeroEmbedding W) := (internalIsCofibrationSequence W).exactH
end Quillen.Waldhausen.ExtensionCategory
