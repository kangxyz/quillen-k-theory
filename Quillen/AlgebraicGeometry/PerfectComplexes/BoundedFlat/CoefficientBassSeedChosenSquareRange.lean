/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedChosenProjectionPaste
public import Quillen.Topology.Path.ParameterBoundarySupport

/-! The exact chosen-square operations preserve the full seed-tip subsets. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
namespace Quillen.PerfectComplexes.CoefficientBassSeedChosenProjectionPaste
open ParameterSupport
variable {X : Type*} [TopologicalSpace X] {U : Set X}

/-- Original inverse-edge cancellation stays in any set containing its whole comparison. -/
theorem closeRight_in {a b c : X} {H : Path a b} {A : Path a c} {B : Path b c}
    {J : H.Homotopy (A.trans B.symm)} (hJ : HomotopyIn U J) :
    HomotopyIn U (closeRight J) := by
  have hA := path_trans_left (hom_target hJ)
  have hB : PathIn U B := by
    simpa only [Path.symm_symm] using path_symm (path_trans_right (hom_target hJ))
  have hc : HomotopyIn U
      (show (B.symm.trans B).Homotopy (Path.refl c) from by
        simpa only [Path.symm_symm] using (Path.Homotopy.reflTransSymm B.symm).symm) := by
    intro z
    have hp : B.symm.trans B.symm.symm = B.symm.trans B := by rw [Path.symm_symm]
    simp only [eq_mp_eq_cast, hom_type_cast_apply hp rfl]
    exact hom_symm (hom_reflTransSymm (path_symm hB)) z
  exact hom_trans (hom_hcomp hJ (hom_refl hB))
    (hom_trans (hom_transAssoc hA (path_symm hB) hB)
      (hom_trans (hom_hcomp (hom_refl hA) hc) (hom_transRefl hA)))

/-- Compact quotient descent adds no new value beyond the original boundary recipe. -/
theorem squareOfBoundary_in {a b c d e f : X}
    {H : Path a b} {L : Path a c} {P : Path c d}
    {K : Path d f} {M : Path e f} {N : Path b e}
    {J : H.Homotopy ((L.trans (P.trans (K.trans M.symm))).trans N.symm)}
    (hJ : HomotopyIn U J) (r s : I) : (squareOfBoundary J).parameter (r, s) ∈ U := by
  have hLPKM := path_trans_left (hom_target hJ)
  have hL := path_trans_left hLPKM
  have hPKM := path_trans_right hLPKM
  have hP := path_trans_left hPKM
  have hKM := path_trans_right hPKM
  have hK := path_trans_left hKM
  have hMs := path_trans_right hKM
  have hc := hom_trans (closeRight_in hJ)
    (hom_trans
      (hom_hcomp (hom_refl hL) (hom_symm (hom_transAssoc hP hK hMs)))
      (hom_symm (hom_transAssoc hL (path_trans hP hK) hMs)))
  obtain ⟨z, hz⟩ := ThreeSideSquare.collapse_surjective (r, s)
  have he := CarrierPathSquare.boundaryParameter_collapse
    ((closeRight J).trans
      (((Path.Homotopy.refl L).hcomp (Path.Homotopy.transAssoc P K M.symm).symm).trans
        (Path.Homotopy.transAssoc L (P.trans K) M.symm).symm)) z
  rw [hz] at he
  exact he.symm ▸ hc z

end Quillen.PerfectComplexes.CoefficientBassSeedChosenProjectionPaste
