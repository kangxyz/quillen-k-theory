import Quillen.Library
import Quillen.Topology.HELP.CubeBoundaryHomeomorph
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Topology.HELP.CubeBoundaryHomeomorph
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless count == 30 do throwError "Expected 30 boundary-homeomorphism origins, found {count}"
  logInfo m!"Audited all {count} boundary-homeomorphism origins."
noncomputable section
open CategoryTheory Quillen Quillen.CubicalTests
open scoped Topology unitInterval
universe u
example {A B : TopCat.{u}} (i : A ⟶ B) (hi : Function.Injective i) :
    Function.Injective (TheoremA.cylinderBoundaryMap i) :=
  TheoremA.cylinderBoundaryMap_injective i hi
example (n : ℕ) : Function.Injective (boundaryPresentation.{u} n).map :=
  boundaryPresentation_injective n
example (n : ℕ) : Topology.IsClosedEmbedding (boundaryPresentation.{u} n).map :=
  boundaryPresentation_isClosedEmbedding n
example (n : ℕ) (a : (boundaryPresentation.{u} n).space) :
    (boundaryPresentationHomeomorph n a).val = (boundaryPresentation n).map a := rfl
example (n : ℕ) (z : boundary.{u} n) :
    (boundaryPresentation n).map ((boundaryPresentationHomeomorph n).symm z) = z.val :=
  boundaryPresentationHomeomorph_symm_map n z
example (n : ℕ) : (TopCat.isoOfHomeo (boundaryPresentationHomeomorph.{u} n)).hom ≫
    boundaryInclusion n = (boundaryPresentation n).map := rfl
example (n : ℕ) : (TopCat.isoOfHomeo (boundaryPresentationHomeomorph.{u} n)).inv ≫
    (boundaryPresentation n).map = boundaryInclusion n :=
  boundaryPresentationHomeomorph_inv_comp n
example (n : ℕ) : TheoremA.homotopyExtensionProperty (boundaryInclusion.{u} n) :=
  boundaryInclusion_hep n
example (n : ℕ) (z : boundary.{u} n) : boundaryInclusion n z = z.val := rfl
example (n : ℕ) (a : (boundaryPresentation.{u} n).space) :
    (boundaryPresentationUnliftedHomeomorph n a).val = ((boundaryPresentation n).map a).down := rfl
example (n : ℕ) (z : {z : Fin n → unitInterval // z ∈ Cube.boundary (Fin n)}) :
    ((boundaryULiftHomeomorph.{u} n).symm z).val.down = z.val := rfl
example (n : ℕ) : TheoremA.homotopyExtensionProperty (unliftedBoundaryInclusion n) :=
  unliftedBoundaryInclusion_hep n
example : IsEmpty (boundary.{u} 0) := ⟨fun z ↦ by
  obtain ⟨i,_⟩ := z.property
  exact Fin.elim0 i⟩
example (n : ℕ) (Z : TopCat.{u}) (f : C(cube.{u} n,Z))
    (H : C(unitInterval × boundary.{u} n,Z))
    (hzero : ∀ a, H (0,a) = f a.val) :
    ∃ K : C(unitInterval × cube.{u} n,Z),
      (∀ b, K (0,b) = f b) ∧ ∀ t a, K (t,a.val) = H (t,a) :=
  TheoremA.homotopyExtensionProperty_continuous (boundaryInclusion_hep n) Z f H hzero
example (n : ℕ) (Z : TopCat.{0}) (f : C(Fin n → unitInterval,Z))
    (H : C(unitInterval × {z : Fin n → unitInterval // z ∈ Cube.boundary (Fin n)},Z))
    (hzero : ∀ a, H (0,a) = f a.val) :
    ∃ K : C(unitInterval × (Fin n → unitInterval),Z),
      (∀ b, K (0,b) = f b) ∧ ∀ t a, K (t,a.val) = H (t,a) :=
  TheoremA.homotopyExtensionProperty_continuous (unliftedBoundaryInclusion_hep n) Z f H hzero
example (n : ℕ) (Z : TopCat.{u}) (g : C((boundaryPresentation.{u} n).space,Z)) :
    ∃ b : C(boundary.{u} n,Z), ∀ a,
      b ⟨(boundaryPresentation n).map a,(boundaryPresentation n).lands a⟩ = g a := by
  refine ⟨g.comp ⟨(boundaryPresentationHomeomorph n).symm,
    (boundaryPresentationHomeomorph n).symm.continuous⟩,?_⟩
  intro a
  change g ((boundaryPresentationHomeomorph n).symm (boundaryPresentationHomeomorph n a)) = g a
  rw [Homeomorph.symm_apply_apply]
