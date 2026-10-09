import Quillen.Waldhausen.ExtensionCategory.Functoriality
import Quillen.Waldhausen.SConstruction.Rows.Functoriality
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.ExtensionCategory.Functoriality,
    `Quillen.Waldhausen.SConstruction.Rows.Functoriality]
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
  unless count == 27 do throwError "Expected 27 exact-postcomposition origins, got {count}"
  unless count == 27 do
    throwError "Expected 27 postcomposition origins, found {count}"
  logInfo m!"Fixed27 independent audit passed: all {count} exact-postcomposition declaration origins."
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v''
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
variable (V : Structure C) (W : Structure D) (U : Structure E) {F : C ⥤ D} {G : D ⥤ E}
  (hF : IsExact V.cof V.weq W.cof W.weq F) (hG : IsExact W.cof W.weq U.cof U.weq G)
namespace ExtensionCategory
example (X : Obj V) : ((postcompose V W hF).obj X).obj.hom = F.map X.obj.hom := rfl
example {X Y : Obj V} (f : X ⟶ Y) :
    ((postcompose V W hF).map f).hom.left = F.map f.hom.left := rfl
example {X Y : Obj V} (f : X ⟶ Y) :
    ((postcompose V W hF).map f).hom.right = F.map f.hom.right := rfl
example {X Y : Obj V} {f : X ⟶ Y} (hf : cof V f) :
    W.cof (relativeMap W ((postcompose V W hF).map f)) := (postcompose_cof V W hF hf).2
example : IsExact (waldhausenStructure V).cof (waldhausenStructure V).weq
    (waldhausenStructure W).cof (waldhausenStructure W).weq (postcompose V W hF) :=
  postcompose_exact V W hF
example : postcompose V W hF ⋙ source W = source V ⋙ F := postcompose_source V W hF
example : postcompose V W hF ⋙ middle W = middle V ⋙ F := postcompose_middle V W hF
example : postcompose V V (IsExact.id V.cof V.weq) = 𝟭 (Obj V) := postcompose_id V
example : postcompose V U (hF.comp hG) = postcompose V W hF ⋙ postcompose W U hG :=
  postcompose_comp V W hF U hG
end ExtensionCategory
namespace QuotientRows
variable (n : SimplexCategory)
example (A : Obj V n) : ((postcompose V W hF n).obj A).obj = A.obj ⋙ F := rfl
example {A B : Obj V n} (η : A ⟶ B) (p : Interval n) :
    ((postcompose V W hF n).map η).hom.app p = F.map (η.hom.app p) := rfl
example {A B : Obj V n} {η : A ⟶ B} (hη : cof V n η) :
    cof W n ((postcompose V W hF n).map η) := postcompose_cof V W hF hη
example : IsExact (waldhausenStructure V n).cof (waldhausenStructure V n).weq
    (waldhausenStructure W n).cof (waldhausenStructure W n).weq (postcompose V W hF n) :=
  postcompose_exact V W hF n
example (p : Interval n) : postcompose V W hF n ⋙ evaluation W p = evaluation V p ⋙ F :=
  postcompose_evaluation V W hF p
example {m : SimplexCategory} (α : m ⟶ n) :
    postcompose V W hF n ⋙ reindex W α = reindex V α ⋙ postcompose V W hF m :=
  postcompose_reindex V W hF α
example : postcompose V V (IsExact.id V.cof V.weq) n = 𝟭 (Obj V n) := postcompose_id V n
example : postcompose V U (hF.comp hG) n = postcompose V W hF n ⋙ postcompose W U hG n :=
  postcompose_comp V W hF U hG n

-- The actual square functor agrees for every triple, including degenerate ones.
example (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    postcompose V W hF n ⋙ horizontalArrow W i j k hij hjk =
      horizontalArrow V i j k hij hjk ⋙ ExtensionCategory.postcompose V W hF :=
  postcompose_horizontalArrow V W hF i j k hij hjk
-- No equality between image chosen zero and target chosen zero is supplied.
example (Z : Obj V n) (hZ : IsZero Z) : IsZero ((postcompose V W hF n).obj Z) :=
  (postcompose_exact V W hF n).zero hZ
-- Every original component weak map is mapped, with no reflection assumption.
example {A B : Obj V n} (η : A ⟶ B) (hη : weq V n η) (p : Interval n) :
    W.weq (F.map (η.hom.app p)) := (postcompose_exact V W hF n).weak η hη p
end QuotientRows
end Quillen.Waldhausen
