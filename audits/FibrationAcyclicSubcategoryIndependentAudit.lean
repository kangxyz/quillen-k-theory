import Quillen.Waldhausen.Fibration.AcyclicSubcategory
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Waldhausen.Fibration.AcyclicSubcategory
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 48 do throwError "Expected 48 acyclic-subcategory origins, got {count}"
  logInfo m!"Audited all {count} acyclic-subcategory declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example : N.coarse.cof = V.cof := N.cof_eq
example : N.coarse.zero = V.zero := N.zero_eq
example : V.weq ≤ N.coarse.weq := N.le_weq
example (X : C) : acyclicObjects N X ↔ N.coarse.weq (N.coarse.isZero.to_ X) := Iff.rfl
example {X Y : AcyclicCategory N} (f : X ⟶ Y) : (acyclicInclusion N).map f = f.hom := rfl
example {X Y : AcyclicCategory N} (f : X ⟶ Y) :
    (acyclicStructure N).cof f ↔ V.cof f.hom := Iff.rfl
example {X Y : AcyclicCategory N} (f : X ⟶ Y) :
    (acyclicStructure N).weq f ↔ V.weq f.hom := Iff.rfl
example : (acyclicInclusion N).obj (acyclicStructure N).zero = V.zero := rfl
example : (acyclicInclusion N).obj (acyclicStructure N).zero = N.coarse.zero :=
  acyclicInclusion_zero_coarse N
example : IsExact (acyclicStructure N).cof (acyclicStructure N).weq V.cof V.weq
    (acyclicInclusion N) := acyclicInclusion_exact N
example : IsExact V.cof V.weq N.coarse.cof N.coarse.weq (𝟭 C) := changeWeak_exact N
example : IsExact (acyclicStructure N).cof (acyclicStructure N).weq
    N.coarse.cof N.coarse.weq (acyclicInclusion N) := acyclicInclusion_coarse_exact N
example {A B D P : AcyclicCategory N} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P}
    (hi : V.cof i.hom) (h : IsPushout i f g j) : IsPushout i.hom f.hom g.hom j.hom :=
  acyclicInclusion_map_pushout N hi h
example (X : ExtensionCategory.Obj V) (hA : Acyclic N.coarse X.obj.left)
    (hB : Acyclic N.coarse X.obj.right) : Acyclic N.coarse ((ExtensionCategory.cofiber V).obj X) :=
  fine_cofiber_acyclic N X hA hB
example [N.coarse.weq.HasTwoOutOfThreeProperty] {X Y : AcyclicCategory N} (f : X ⟶ Y) :
    N.coarse.weq ((acyclicInclusion N).map f) := acyclicInclusion_map_coarse_weak N f
end Quillen.Waldhausen.Fibration

namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
-- Genuine ambient closure, without saturation or an extension axiom.
example {A B D P : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P}
    (hi : V.cof i) (h : IsPushout i f g j)
    (hA : acyclicObjects N A) (hB : acyclicObjects N B) (hD : acyclicObjects N D) :
    acyclicObjects N P := acyclic_of_isPushout N.coarse (by rwa [N.cof_eq]) h hA hB hD
example {A B D : AcyclicCategory N} (i : A ⟶ B) (f : A ⟶ D)
    (hi : (acyclicStructure N).cof i) :
    ∃ (P : AcyclicCategory N) (g : B ⟶ P) (j : D ⟶ P),
      IsPushout i f g j ∧ IsPushout i.hom f.hom g.hom j.hom :=
  acyclic_pushout_exists N i f hi
-- Fine weak equivalences remain exactly the ambient fine class, not all maps.
example : (acyclicStructure N).weq = V.weq.inverseImage (acyclicInclusion N) := rfl
end Quillen.Waldhausen.Fibration
