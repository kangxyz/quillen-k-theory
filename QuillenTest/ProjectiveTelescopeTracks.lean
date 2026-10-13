/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.KTheory.Plus.ProjectiveTelescopeTracks

/-! # The two literal finite-stage routes have a common original endpoint -/

open CategoryTheory MonoidalCategory Quillen Quillen.FiniteProjectiveModule
universe u
noncomputable section
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric

example (R : Type u) [Ring R] (P Q : IsoCategory Rᵐᵒᵖ) (k : ℕ)
    (f : P ⊗ Q ≅ freeIso Rᵐᵒᵖ k) :
    projectiveTrackSource R P k ≅ projectiveTrackTarget R P Q :=
  projectiveUpperTrack R P Q k f

example (R : Type u) [Ring R] (P Q : IsoCategory Rᵐᵒᵖ) (k : ℕ)
    (f : P ⊗ Q ≅ freeIso Rᵐᵒᵖ k) :
    projectiveTrackSource R P k ≅ projectiveTrackTarget R P Q :=
  projectiveLowerTrack R P Q k f

example (R : Type u) [Ring R] (P Q : IsoCategory Rᵐᵒᵖ) (n : ℕ)
    (x y : ClassifyingSpace (ProjectiveStage R)) :
    Joined (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)
        (classifyingSpaceMap (projectiveTrackTarget R P Q) x))
      (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)
        (classifyingSpaceMap (projectiveTrackTarget R P Q) y)) ↔
    Joined (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) x)
      (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) y) :=
  projectiveTrackTarget_infinite_joined_iff R P Q n x y
