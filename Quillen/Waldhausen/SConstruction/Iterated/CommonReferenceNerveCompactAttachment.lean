/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactFamily
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveWhiskering
public import Quillen.Waldhausen.SConstruction.Iterated.ModelReferenceReanchor

/-!
# Exact evaluation of compact common-reference attachments

An actual postcomposition followed by a specified reference transport defines a map on full
dependent nodes. Its whole compact family evaluates to the original postcomposed family,
at every native level and the unchanged parameter. The reference transport may be shifted
by any specified source automorphism; no equality between the resulting carrier nodes is used.
This owner supplies no mapping-cone evaluator, boundary lift, or higher comparison.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Convexity
open scoped Simplicial Topology
universe u v

namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve
variable {V W Z : Model.{u}} (F : V ⟶ W) (J : W ⟶ Z) (G : V ⟶ Z)
  (ε : G.functor ≅ (F ≫ J).functor)

/-- Attach the actual postcomposed node using its complete specified reference. -/
def attachPostcompNode (N : Node F) : Node G :=
  ⟨N.1 ≫ J, ε ≪≫ isoWhiskerRight N.2 J.functor⟩

/-- Common reanchoring cancels inside the whole finite diagram, retaining the original
postcomposition at the unchanged simplex point and every native level. -/
theorem prespectrumFamily_attachPostcomp {k : ℕ} (N : Fin (k + 1) → Node F)
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    prespectrumFamily G (fun i ↦ attachPostcompNode F J G ε (N i)) n (z, x) =
      (prespectrumMap J).map n (prespectrumFamily F N n (z, x)) := by
  calc
    _ = prespectrumFamily (F ≫ J) (fun i ↦ postcompNode J (N i)) n (z, x) := by
      rw [prespectrumFamily_eq, prespectrumFamily_eq]
      change prespectrumSimplexFamily
        (ModelSimplex.reanchorSimplex ε (fun i ↦ postcompNode J (N i))) n (z, x) = _
      rw [ModelSimplex.reanchorSimplex_eq]
    _ = _ := prespectrumFamily_postcomp N J n z x

variable {S : Type v} [TopologicalSpace S] [CompactSpace S]

/-- Every compact parameter is evaluated after the actual attaching map, without changing
its parameter, native input, or level, including degree zero. -/
theorem compactPrespectrumFamily_attachPostcomp
    (p : C(S, |nerve (Codiscrete (Node F))|)) (n : ℕ) (t : S)
    (x : (prespectrum V).space n) :
    compactPrespectrumFamily G ((mapParameter (attachPostcompNode F J G ε)).comp p)
        n (t, x) =
      (prespectrumMap J).map n (compactPrespectrumFamily F p n (t, x)) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F (p t)
  have hp : ((mapParameter (attachPostcompNode F J G ε)).comp p) t =
      parameter G (fun i ↦ attachPostcompNode F J G ε (N i)) z := by
    change mapParameter (attachPostcompNode F J G ε) (p t) = _
    rw [← hz, mapParameter_parameter]
  rw [compactPrespectrumFamily_eq_simplex G _ _ t z hp n x,
    compactPrespectrumFamily_eq_simplex F p N t z hz.symm n x]
  exact prespectrumFamily_attachPostcomp F J G ε N n z x

/-- The entire joint continuous family is the original postcomposition, not merely an
endpoint or a chosen finite collection of parameter values. -/
theorem compactPrespectrumFamily_attachPostcomp_map
    (p : C(S, |nerve (Codiscrete (Node F))|)) (n : ℕ) :
    compactPrespectrumFamily G ((mapParameter (attachPostcompNode F J G ε)).comp p) n =
      ((prespectrumMap J).map n).comp (compactPrespectrumFamily F p n) := by
  apply ContinuousMap.ext
  rintro ⟨t, x⟩
  exact compactPrespectrumFamily_attachPostcomp F J G ε p n t x

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve
