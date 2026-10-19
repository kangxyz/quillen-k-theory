/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactFamily
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveWhiskering
public import Quillen.Waldhausen.SConstruction.Iterated.ModelReferenceReanchor

/-!
# Exact compact common-reference attachments under precomposition

The original model map and a specified complete reference transport act on whole dependent
nodes. Their compact family is exactly the original family evaluated on the precomposed
native input, with both the parameter and spectrum level unchanged. This proves no equality
between differently anchored nodes and supplies no higher filler.
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
variable {V W T : Model.{u}} (F : V ⟶ W) (J : T ⟶ V) (G : T ⟶ W)
  (ε : G.functor ≅ (J ≫ F).functor)

/-- Attach the original precomposed node with its entire specified reference isomorphism. -/
def attachPrecompNode (N : Node F) : Node G :=
  ⟨J ≫ N.1, ε ≪≫ isoWhiskerLeft J.functor N.2⟩

/-- Reanchoring cancels inside the finite diagram and keeps the actual precomposed input. -/
theorem prespectrumFamily_attachPrecomp {k : ℕ} (N : Fin (k + 1) → Node F)
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum T).space n) :
    prespectrumFamily G (fun i ↦ attachPrecompNode F J G ε (N i)) n (z, x) =
      prespectrumFamily F N n (z, (prespectrumMap J).map n x) := by
  calc
    _ = prespectrumFamily (J ≫ F) (fun i ↦ precompNode J (N i)) n (z, x) := by
      rw [prespectrumFamily_eq, prespectrumFamily_eq]
      change prespectrumSimplexFamily
        (ModelSimplex.reanchorSimplex ε (fun i ↦ precompNode J (N i))) n (z, x) = _
      rw [ModelSimplex.reanchorSimplex_eq]
    _ = _ := prespectrumFamily_precomp N J n z x

variable {S : Type v} [TopologicalSpace S] [CompactSpace S]

/-- The whole compact attachment retains the original parameter and every native input level. -/
theorem compactPrespectrumFamily_attachPrecomp
    (p : C(S, |nerve (Codiscrete (Node F))|)) (n : ℕ) (t : S)
    (x : (prespectrum T).space n) :
    compactPrespectrumFamily G ((mapParameter (attachPrecompNode F J G ε)).comp p)
        n (t, x) =
      compactPrespectrumFamily F p n (t, (prespectrumMap J).map n x) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F (p t)
  have hp : ((mapParameter (attachPrecompNode F J G ε)).comp p) t =
      parameter G (fun i ↦ attachPrecompNode F J G ε (N i)) z := by
    change mapParameter (attachPrecompNode F J G ε) (p t) = _
    rw [← hz, mapParameter_parameter]
  rw [compactPrespectrumFamily_eq_simplex G _ _ t z hp n x,
    compactPrespectrumFamily_eq_simplex F p N t z hz.symm n ((prespectrumMap J).map n x)]
  exact prespectrumFamily_attachPrecomp F J G ε N n z x

/-- The full jointly continuous family is the actual precomposition at the same parameter. -/
theorem compactPrespectrumFamily_attachPrecomp_map
    (p : C(S, |nerve (Codiscrete (Node F))|)) (n : ℕ) :
    compactPrespectrumFamily G ((mapParameter (attachPrecompNode F J G ε)).comp p) n =
      (compactPrespectrumFamily F p n).comp
        ⟨fun z ↦ (z.1, (prespectrumMap J).map n z.2), by fun_prop⟩ := by
  apply ContinuousMap.ext
  rintro ⟨t, x⟩
  exact compactPrespectrumFamily_attachPrecomp F J G ε p n t x

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve
