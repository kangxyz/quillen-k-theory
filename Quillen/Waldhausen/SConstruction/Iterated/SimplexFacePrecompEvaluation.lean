/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleLift
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexWhiskering
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Evaluation of a whole precomposed simplex face

An equality of complete Model diagrams transports an already chosen two-parameter family.
The parameters and all levels, including the degree-zero loop coordinate, are unchanged.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS

/-- A whole face equality transports the original relative homotopy under precomposition. -/
theorem prespectrumSimplexFamily_face_precomp
    {V W T : Model.{u}} {k l : ℕ}
    (R : ModelSimplex V W l) (S : ModelSimplex T W k) (J : T ⟶ V)
    (α : ⦋l⦌ ⟶ ⦋k⦌) (hface : S.face α = R.precomp J)
    (P : C(unitInterval × unitInterval, StdSimplex ℝ (Fin (l + 1))))
    {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
    (N : H.RelHomotopy K)
    (hN : ∀ (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n),
      prespectrumSimplexFamily R n (P (r, s), x) = N.level n (r, (s, x)))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    prespectrumSimplexFamily S n (StdSimplex.map α.toOrderHom (P (r, s)), x) =
      (Homotopy.RelHomotopy.precomp (prespectrumMap J) N).level n (r, (s, x)) := by
  exact (prespectrumSimplexFamily_face S α n (P (r, s)) x).trans
    ((congrArg (fun Q => prespectrumSimplexFamily Q n (P (r, s), x)) hface).trans
      ((prespectrumSimplexFamily_precomp R J n (P (r, s)) x).trans
        (hN n r s ((prespectrumMap J).map n x))))

end Quillen.Waldhausen.IteratedS
