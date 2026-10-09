import Quillen.Topology.Realization.DoubleCylinderCompactGraph
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.Realization.DoubleCylinder,
    `Quillen.Topology.Realization.DoubleCylinderCompactGraph]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    seen := seen.insert origin
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axs}"
  unless seen.size == 2 do throwError "Missing double-cylinder origin"
  unless count == 40 do throwError "Expected 40 double-cylinder origins, found {count}"
  logInfo m!"Audited all {count} double-cylinder realization origins."
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Quillen Quillen.DoubleCylinder
open scoped Simplicial Topology
universe u v w z
variable {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
  {T : TopCat.{u}} {l : |X| ⊗ TopCat.I ⟶ T} {e : TopCat.of (|Y| ⊕ |Z|) ⟶ T}
  (sq : IsPushout (TheoremA.intervalEndpoints |X|)
    (endMap (SSet.toTop.map f) (SSet.toTop.map g)) l e)
example : |simplicial f g| ≅ T := realizationIso f g sq
example : |simplicial f g| ≃ₜ T := realizationHomeomorph f g sq
example (x : |X| ⊗ TopCat.I) :
    realizationHomeomorph f g sq (realizedCylinder f g x) = l x :=
  realizationHomeomorph_cylinder f g sq x
example (y : |Y|) :
    realizationHomeomorph f g sq (realizedEnds f g (Sum.inl y)) = e (Sum.inl y) :=
  realizationHomeomorph_ends f g sq _
example (z : |Z|) :
    realizationHomeomorph f g sq (realizedEnds f g (Sum.inr z)) = e (Sum.inr z) :=
  realizationHomeomorph_ends f g sq _
example (t : T) : realizationHomeomorph f g sq ((realizationHomeomorph f g sq).symm t) = t :=
  (realizationHomeomorph f g sq).apply_symm_apply t
example (t : |simplicial f g|) :
    (realizationHomeomorph f g sq).symm (realizationHomeomorph f g sq t) = t :=
  (realizationHomeomorph f g sq).symm_apply_apply t
example : SSet.toTop.map (simplicialCylinder f g) ≫ (realizationIso f g sq).hom =
    (realizationCylinderIso X).hom ≫ l := realizationIso_cylinder f g sq
example : SSet.toTop.map (simplicialEnds f g) ≫ (realizationIso f g sq).hom =
    (realizationBinarySumIso Y Z).hom ≫ e := realizationIso_ends f g sq
example {D : Type v} [TopologicalSpace D] [CompactSpace D] (b : C(D,T)) :
    IsClosed (Set.ofPred (fun z : D × T ↦ b z.1 = z.2)) :=
  compactMap_isClosed_graph f g sq b
example {P : Type w} {D : Type v} [TopologicalSpace P] [TopologicalSpace D]
    [CompactSpace D] (p : C(P,T)) (b : C(D,T)) :
    IsClosed (Set.ofPred (fun z : P × D ↦ p z.1 = b z.2)) :=
  compactMap_matching_isClosed f g sq p b
example {E : Type z} {P : Type w} {D : Type v}
    [TopologicalSpace E] [TopologicalSpace P] [TopologicalSpace D]
    [CompactSpace D] [LocallyCompactSpace D] {q : E → P} (hq : Topology.IsQuotientMap q)
    (p : C(P,T)) (b : C(D,T)) :
    Topology.IsQuotientMap (fun z : {z : E × D // p (q z.1) = b z.2} ↦
      (⟨(q z.1.1,z.1.2),z.2⟩ : {z : P × D // p z.1 = b z.2})) :=
  compactMap_pullback_quotient f g sq hq p b
