import Quillen.Topology.Pushout.CompactParameterSquare
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Topology.Pushout.CompactParameterSquare
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless count == 48 do throwError "Expected 48 compact-parameter square origins, got {count}"
  logInfo m!"FIXED48 PASSED {count}"
noncomputable section
open CategoryTheory Limits Topology MonoidalCategory Quillen Quillen.CompactParameterPushout
open scoped Topology Simplicial
universe u
variable {A B C P T : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ P} {j : C ⟶ P}
  (sq : IsPushout i f g j) (base : C(P,T))
  {D : Type u} [TopologicalSpace D] (b : C(D,T))
example (z : Source (i := i) (g := g) base b) : (leftLeg base b z).val = (i z.val.1,z.val.2) := rfl
example (z : Source (i := i) (g := g) base b) : (rightLeg sq base b z).val = (f z.val.1,z.val.2) := rfl
example (z : Left (g := g) base b) : (leftInclusion base b z).val = (g z.val.1,z.val.2) := rfl
example (z : Right (j := j) base b) : (rightInclusion base b z).val = (j z.val.1,z.val.2) := rfl
example (z : Source (i := i) (g := g) base b) :
    (leftInclusion base b (leftLeg base b z)).val.2 = z.val.2 := rfl
example (z : Source (i := i) (g := g) base b) :
    (rightInclusion base b (rightLeg sq base b z)).val.2 = z.val.2 := rfl
example : leftLeg base b ≫ leftInclusion base b = rightLeg sq base b ≫ rightInclusion base b :=
  square sq base b
section LocallyCompact
variable [LocallyCompactSpace D]
  (hc : IsClosed (Set.ofPred (fun z : P × D ↦ base z.1 = b z.2)))
include sq in
example : IsQuotientMap
    (Sum.elim (leftInclusion (g := g) base b) (rightInclusion (j := j) base b)) :=
  sum_isQuotientMap sq base b hc
example : IsPushout (leftLeg base b) (rightLeg sq base b) (leftInclusion base b) (rightInclusion base b) :=
  isPushout sq base b hc
example [IsEmpty D] :
    IsPushout (leftLeg base b) (rightLeg sq base b) (leftInclusion base b) (rightInclusion base b) :=
  isPushout sq base b hc
example (hb : IsClosed (Set.ofPred (fun z : D × T ↦ b z.1 = z.2))) :
    IsPushout (leftLeg base b) (rightLeg sq base b) (leftInclusion base b) (rightInclusion base b) :=
  isPushout_of_closedGraph sq base b hb
variable {Z : TopCat.{u}} (l : Left (g := g) base b ⟶ Z) (r : Right (j := j) base b ⟶ Z)
  (w : leftLeg base b ≫ l = rightLeg sq base b ≫ r)
example : leftInclusion base b ≫ desc sq base b l r w hc = l := left_desc sq base b l r w hc
example : rightInclusion base b ≫ desc sq base b l r w hc = r := right_desc sq base b l r w hc
example (m : Vertex base b ⟶ Z)
    (hm₁ : leftInclusion base b ≫ m = l) (hm₂ : rightInclusion base b ≫ m = r) :
    m = desc sq base b l r w hc :=
  (isPushout sq base b hc).hom_ext (hm₁.trans (left_desc sq base b l r w hc).symm)
    (hm₂.trans (right_desc sq base b l r w hc).symm)
example (l₀ : Left (g := g) base b ⟶ TopCat.of PEmpty.{u+1})
    (r₀ : Right (j := j) base b ⟶ TopCat.of PEmpty.{u+1})
    (w₀ : leftLeg base b ≫ l₀ = rightLeg sq base b ≫ r₀) :
    Vertex base b ⟶ TopCat.of PEmpty.{u+1} := desc sq base b l₀ r₀ w₀ hc
end LocallyCompact
section RealizationTests
variable [CompactSpace D] [LocallyCompactSpace D] (X : SSet.{u})
example (p : C(P,|X|)) (t : C(D,|X|)) :
    IsPushout (leftLeg p t) (rightLeg sq p t) (leftInclusion p t) (rightInclusion p t) :=
  isPushout_realization sq X p t
example (p : C(P,|X|)) (t : C(ULift.{u} PUnit,|X|)) :
    IsPushout (leftLeg p t) (rightLeg sq p t) (leftInclusion p t) (rightInclusion p t) :=
  isPushout_realization sq X p t
example (n : ℕ) (p : C(P,|X|)) (t : C(ULift.{u} (Fin n → unitInterval),|X|)) :
    IsPushout (leftLeg p t) (rightLeg sq p t) (leftInclusion p t) (rightInclusion p t) :=
  isPushout_realization sq X p t
example (p : C(P,|X|)) (t : C(ULift.{u} (Fin 0 → unitInterval),|X|)) :
    IsPushout (leftLeg p t) (rightLeg sq p t) (leftInclusion p t) (rightInclusion p t) :=
  isPushout_realization sq X p t
example {X Y Z : SSet.{u}} (f₀ : X ⟶ Y) (g₀ : X ⟶ Z)
    {l₀ : |X| ⊗ TopCat.I ⟶ T} {e₀ : TopCat.of (|Y| ⊕ |Z|) ⟶ T}
    (sqT : IsPushout (TheoremA.intervalEndpoints |X|)
      (DoubleCylinder.endMap (SSet.toTop.map f₀) (SSet.toTop.map g₀)) l₀ e₀) :
    IsPushout (leftLeg base b) (rightLeg sq base b) (leftInclusion base b) (rightInclusion base b) :=
  isPushout_doubleCylinder sq base b f₀ g₀ sqT
end RealizationTests

section IndependentChecks
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
example (z : Source (i := i) (g := g) base b) :
    base (j (rightLeg sq base b z).val.1) = b (rightLeg sq base b z).val.2 :=
  (rightLeg sq base b z).property
example [IsEmpty D] : IsEmpty (Vertex base b) := ⟨fun z ↦ isEmptyElim z.val.2⟩
variable [LocallyCompactSpace D]
  (hc : IsClosed (Set.ofPred (fun z : P × D ↦ base z.1 = b z.2)))
example {Z : TopCat.{u}} (l : Left (g := g) base b ⟶ Z) (r : Right (j := j) base b ⟶ Z)
    (w : leftLeg base b ≫ l = rightLeg sq base b ≫ r) (z : Left (g := g) base b) :
    desc sq base b l r w hc (leftInclusion base b z) = l z :=
  ConcreteCategory.congr_hom (left_desc sq base b l r w hc) z
example {Z : TopCat.{u}} (l : Left (g := g) base b ⟶ Z) (r : Right (j := j) base b ⟶ Z)
    (w : leftLeg base b ≫ l = rightLeg sq base b ≫ r) (z : Right (j := j) base b) :
    desc sq base b l r w hc (rightInclusion base b z) = r z :=
  ConcreteCategory.congr_hom (right_desc sq base b l r w hc) z
example {Z : TopCat.{u}} [IsEmpty Z]
    (l : Left (g := g) base b ⟶ Z) (r : Right (j := j) base b ⟶ Z)
    (w : leftLeg base b ≫ l = rightLeg sq base b ≫ r) : IsEmpty (Vertex base b) :=
  ⟨fun z ↦ isEmptyElim (desc sq base b l r w hc z)⟩
example :
    let l : Left (g := g) base b ⟶ TopCat.of D := TopCat.ofHom ⟨fun z ↦ z.val.2,by fun_prop⟩
    let r : Right (j := j) base b ⟶ TopCat.of D := TopCat.ofHom ⟨fun z ↦ z.val.2,by fun_prop⟩
    desc sq base b l r rfl hc = TopCat.ofHom ⟨fun z ↦ z.val.2,by fun_prop⟩ := by
  dsimp only
  apply (isPushout sq base b hc).hom_ext
  · exact left_desc sq base b _ _ rfl hc
  · exact right_desc sq base b _ _ rfl hc
end IndependentChecks
section NoncompactParameter
example (t : C(ULift.{u} ℝ,T))
    (hc : IsClosed (Set.ofPred (fun z : P × ULift.{u} ℝ ↦ base z.1 = t z.2))) :
    IsPushout (leftLeg base t) (rightLeg sq base t)
      (leftInclusion base t) (rightInclusion base t) := by
  let : LocallyCompactSpace (ULift.{u} ℝ) :=
    (Homeomorph.ulift (X := ℝ)).isClosedEmbedding.locallyCompactSpace
  exact isPushout sq base t hc
end NoncompactParameter
