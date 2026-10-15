/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberPasting

/-!
# The original scalar-cofiber loop orientation

The loop produced by the existing iterated-fiber map is compared with the reverse of the
original scalar square. The proof uses the actual cofiber and composition triangles, the
original fine projection, and the prescribed identity-cofiber suffix. This loop-space
statement retains the chosen object component. Passage to a specified Laurent localization
boundary and its normalized homotopy-group class remains a separate comparison.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry unitInterval
open Quillen.Waldhausen.Fibration
open scoped Topology
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (K : Perfect X)

/-- The existing iterated-fiber loop has exactly the displayed original three-path formula. -/
theorem perfectScalarCofiberBoundaryLoop_normalized :
    perfectScalarCofiberBoundaryLoop j r q hq K =
      ((perfectScalarCofiberCoarsePath j r K).trans
        (perfectScalarProjectionCoarsePath j r K)).symm.trans
        ((perfectScalarCofiberPrefixPath j r q hq K).symm.trans
          ((perfectOpenNested j).coarse.identityCofiberSuffixPath K)) := by
  rw [perfectScalarCofiberBoundaryLoop_eq]
  apply Path.ext
  funext s
  rw [Path.trans_apply]
  split_ifs with hs
  · rw [Path.trans_apply, dite_eq_left hs]
    exact ContinuousMap.congr_fun (perfectScalarCofiberSourceLoopPath_changeWeak j r K)
      (unitInterval.symm ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩)
  · rw [Path.trans_apply, dite_eq_right hs]
    change (canonicalFiberObjectPrefixTransport (perfectOpenNested j) K
      (perfectOpenScalarCofiberAcyclic j r q hq K)).val.2 _ = _
    rw [canonicalFiberObjectPrefixTransport_path]
    change ((HomotopyFiber.toPath _ _ (canonicalFiberObjectPrefixed (perfectOpenNested j) K
      (perfectOpenScalarCofiberAcyclic j r q hq K))).trans
        ((perfectOpenNested j).coarse.identityCofiberSuffixPath K)) _ = _
    rw [Path.trans_apply]
    split_ifs with ht
    · rw [Path.trans_apply, dite_eq_left ht]
      exact ContinuousMap.congr_fun (perfectScalarCofiberPrefixedPath_eq j r q hq K) _
    · rw [Path.trans_apply, dite_eq_right ht]

/-- The actual two triangle pastings identify the original iterated-fiber loop with the reversed
scalar square, at its unchanged original object-loop component. -/
def perfectScalarCofiberBoundaryOrientation :
    (perfectScalarCofiberBoundaryLoop j r q hq K).Homotopy
      (perfectScalarWeakLoop j r q hq K).symm := by
  let P := perfectScalarCofiberPrefixPath j r q hq K
  let F := (perfectScalarCofiberCoarsePath j r K).trans
    (perfectScalarProjectionCoarsePath j r K)
  let E := (perfectOpenNested j).coarse.identityCofiberSuffixPath K
  let T := perfectScalarWeakLoop j r q hq K
  have h := perfectScalarCofiberPastingTrack j r q hq K
  have hr : (F.symm.trans P.symm).Homotopy (T.symm.trans E.symm) :=
    h.symm₂.cast (Path.trans_symm P F) (Path.trans_symm E T)
  have hc : (E.symm.trans E).Homotopy (Path.refl _) :=
    (Path.Homotopy.reflTransSymm E.symm).symm.cast (by rw [Path.symm_symm]) rfl
  have H := (Path.Homotopy.transAssoc F.symm P.symm E).symm.trans
    ((hr.hcomp (Path.Homotopy.refl E)).trans
      ((Path.Homotopy.transAssoc T.symm E.symm E).trans
        (((Path.Homotopy.refl T.symm).hcomp hc).trans (Path.Homotopy.transRefl T.symm))))
  exact H.cast (perfectScalarCofiberBoundaryLoop_normalized j r q hq K).symm rfl

end Quillen.PerfectComplexes
