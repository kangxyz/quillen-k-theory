/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberCanonicalSumCube

/-! # Actual compact target and whole reversed canonical-sum consumers -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.ExtensionCategory MonoidalCategory
open scoped Topology Simplicial
universe u
namespace QuillenTest.ScalarCofiberCanonicalSumCube
local instance canonicalSumCoproducts (X : Scheme.{u}) : HasBinaryCoproducts (Perfect X) :=
  Additivity.hasBinaryCoproducts (perfectWaldhausen X)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
    (subdivisionBasepoint (perfectWaldhausen X)))
local notation "V" => perfectWaldhausen X
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
local notation "PV" => productStructure V V
local notation "S" => OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V

/-- The same identity rebase uses the distinct original right subdivision restriction. -/
theorem original_right_coordinate (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCanonicalRightCube j n p z =
      deloopingMap (perfectOpenScalarIdentityRebase_fineExact j)
        (separatedRightDeloopingMap V (p z)) := rfl

/-- The actual public acyclic cone uses the original first restriction. -/
theorem original_acyclic_coordinate (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCanonicalAcyclicCube j r q hq n p z =
      deloopingMap (perfectOpenScalarConeFunctor_waldhausenExact j r q hq).rebase
        (separatedFirstDeloopingMap V (p z)) := rfl

/-- The canonical-null source is transported by the actual inclusion/change-weak equality. -/
theorem original_null_source :
    perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarCanonicalConeCube j r q hq n p) =
      perfectOpenScalarCanonicalCoarseConeCube j r q hq n p :=
  perfectOpenScalarCanonicalConeCube_changeWeak j r q hq n p

/-- The displayed null is literally the old null with the correctly directed source cast. -/
theorem original_null_cast :
    perfectOpenScalarCanonicalNullPath j r q hq n p =
      (perfectOpenScalarCanonicalNullRaw j r q hq n p).cast
        (perfectOpenScalarCanonicalConeCube_changeWeak j r q hq n p) rfl := rfl

/-- Every null time and spatial coordinate is the original canonical null. -/
theorem original_entire_null (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCanonicalNullPath j r q hq n p t z =
      acyclicNullhomotopy N (t, perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) :=
  perfectOpenScalarCanonicalNullPath_apply j r q hq n p t z

/-- The actual fine zero target has the exact compact zero/right endpoint. -/
theorem original_zero_compact_target :
    perfectOpenScalarZeroPairTargetCube j n p =
      coproductCube V n GenLoop.const (perfectOpenScalarCanonicalRightCube j n p) :=
  perfectOpenScalarZeroPairTargetCube_compact j n p

/-- The actual fine cone target has the exact compact cone/right endpoint. -/
theorem original_cone_compact_target :
    perfectOpenScalarConePairTargetCube j r q hq n p =
      coproductCube V n (perfectOpenScalarCanonicalConeCube j r q hq n p)
        (perfectOpenScalarCanonicalRightCube j n p) :=
  perfectOpenScalarConePairTargetCube_compact j r q hq n p

/-- The original zero target is recovered before changing its diagonal endpoint presentation. -/
theorem original_zero_diagonal_target (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarZeroPairTargetCube j n p z =
      SSet.toTop.map (bisimplicialDiagonalIso V).hom
        (realizedDiagonalMap (separatedPairMap V ≫
          bisimplicialSSetMap (PV).cof (PV).weq
            (perfectOpenScalarZeroPairTarget_exact j)) (p z)) :=
  perfectOpenScalarZeroPairTargetCube_diagonal j n p z

/-- The original cone target is recovered on the entire unchanged subdivision cube. -/
theorem original_cone_diagonal_target (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarConePairTargetCube j r q hq n p z =
      SSet.toTop.map (bisimplicialDiagonalIso V).hom
        (realizedDiagonalMap (separatedPairMap V ≫
          bisimplicialSSetMap (PV).cof (PV).weq
            (perfectOpenScalarConePairTarget_exact j r q hq)) (p z)) :=
  perfectOpenScalarConePairTargetCube_diagonal j r q hq n p z

/-- The full ordinary sum cylinder is the actual coproduct image of the pair cylinder. -/
theorem original_whole_coproduct_cylinder :
    (perfectOpenScalarCanonicalPairHomotopy j r q hq).h ≫
        sSetMap (coproductRebasedFunctor_exact W) =
      (perfectOpenScalarCanonicalSumHomotopy j r q hq).h :=
  perfectOpenScalarCanonicalSumCylinder_postcompose j r q hq

/-- The full original diagonal cylinder retains the actual separated pair map. -/
theorem original_whole_diagonal_cylinder :
    (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq).h ≫
        (bisimplicialDiagonalIso W).hom =
      (TheoremA.diagonalMap (separatedPairMap V) ≫ (bisimplicialDiagonalIso PV).hom) ▷ Δ[1] ≫
        (perfectOpenScalarCanonicalSumHomotopy j r q hq).h :=
  perfectOpenScalarCanonicalSumDiagonalCylinder j r q hq

/-- The actual realization retains every original cylinder time and original input. -/
theorem original_whole_realization (t : unitInterval) (x : |TheoremA.diagonalSSet S|) :
    SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (t, x)) =
      coproductBasedMap W (perfectOpenScalarCanonicalPairRealization j r q hq
        (t, separatedPairDeloopingMap V x)) :=
  perfectOpenScalarCanonicalSumDiagonalRealization j r q hq t x

/-- Both projections of the reversed product cylinder retain the full null and fixed right cube. -/
theorem original_reversed_pair (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    Product.deloopingComparison W W
      (perfectOpenScalarCanonicalPairRealization j r q hq
        (unitInterval.symm t, separatedPairDeloopingMap V (p z))) =
      (perfectOpenScalarCanonicalNullPath j r q hq n p t z,
        perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarCanonicalRightCube j n p) z) :=
  perfectOpenScalarCanonicalPairRealization_reversed_projection j r q hq n p t z

/-- The full reversed canonical sum edge is the actual compact null/right path. -/
theorem original_reversed_compact_path (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (unitInterval.symm t, p z)) =
      coproductCubePath W n (perfectOpenScalarCanonicalNullPath j r q hq n p)
        (Path.refl (perfectOpenScalarCubeChangeWeak j n
          (perfectOpenScalarCanonicalRightCube j n p))) t z :=
  perfectOpenScalarCanonicalSumDiagonalRealization_reversed_compact j r q hq n p t z

/-- One spatial coordinate retains the whole boundary at every canonical-null time. -/
theorem original_degree_zero_boundary
    (p₀ : GenLoop (Fin 1) |TheoremA.diagonalSSet S| (subdivisionBasepoint V))
    (t : unitInterval) (z : Fin 1 → unitInterval) (hz : z ∈ Cube.boundary (Fin 1)) :
    SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (unitInterval.symm t, p₀ z)) = (W).kBasepoint :=
  perfectOpenScalarCanonicalSumDiagonalRealization_reversed_boundary j r q hq 0 p₀ t z hz

end QuillenTest.ScalarCofiberCanonicalSumCube
