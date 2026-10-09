import Quillen.CategoryTheory.TheoremB.NormalizedFirstCollar
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == `Quillen.CategoryTheory.TheoremB.NormalizedFirstCollar do continue
    count := count + 1
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless count == 51 do
    throwError "Expected exactly 51 defining origins, found {count}"
  logInfo m!"Audited all {count} actual first-pushout collar origins."
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Quillen
open scoped Topology unitInterval
universe u
variable {T : TopCat.{u}} {U V : Set T} (d : NormalizedOpenGluing.Data T U V)
  (h : C(d.M,I)) (hi : ∀ a,h (d.i0 a) = 1) (cut : I) (hc : cut < 1)
example (m : d.M) : (d.firstCollarHeight h hi (d.firstBridge m)).down = h m :=
  d.firstCollarHeight_bridge h hi m
example (e : d.E0) : (d.firstCollarHeight h hi (d.firstEnd e)).down = 1 :=
  d.firstCollarHeight_end h hi e
example : IsOpen (d.firstEndCollarSet h hi cut) := d.firstEndCollar_isOpen h hi cut
example : IsPushout (d.bridgeEndCollarEnd h hi cut hc) d.inclusion0
    (d.firstEndCollarBridge h hi cut) (d.firstEndCollarEnd h hi cut hc) :=
  d.firstEndCollar_isPushout h hi cut hc
example (m : d.BridgeEndCollar h cut) :
    (d.firstEndCollarBridge h hi cut m).val = d.firstBridge m.val := rfl
example (e : d.E0) : (d.firstEndCollarEnd h hi cut hc e).val = d.firstEnd e := rfl
example : d.firstEndCollarEnd h hi cut hc ≫ d.firstEndCollarProjection h hi cut = d.p0 :=
  d.firstEndCollarEnd_projection h hi cut hc
example (R : TheoremA.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc)) :
    (d.firstEndCollarStrongDeformationRetract h hi cut hc R).toHomotopyEquiv.toFun =
      (d.firstEndCollarEnd h hi cut hc).hom := rfl
example (R : TheoremA.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc))
    (hR : R.H ≫ d.bridgeEndCollarBase h cut =
      fst (d.BridgeEndCollar h cut) TopCat.I ≫ d.bridgeEndCollarBase h cut) :
    (d.firstEndCollarStrongDeformationRetract h hi cut hc R).H ≫
      d.firstEndCollarBase h hi cut =
      fst (d.FirstEndCollar h hi cut) TopCat.I ≫ d.firstEndCollarBase h hi cut :=
  d.firstEndCollarStrongDeformationRetract_over h hi cut hc R hR
example (x : d.First) (hx : d.firstBase x ∉ V) : x ∈ d.firstEndCollarSet h hi cut :=
  d.firstEndCollar_contains_complement h hi cut hc x hx
example : d.firstEndCollarSet h hi cut ∪ d.firstBase ⁻¹' V = Set.univ :=
  d.firstEndCollar_cover h hi cut hc
example (hv : V = ∅) : d.firstEndCollarSet h hi cut = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact d.firstEndCollar_contains_complement h hi cut hc x (by intro hx; have he : d.firstBase x ∈ (∅ : Set T) := hv ▸ hx; exact he)
