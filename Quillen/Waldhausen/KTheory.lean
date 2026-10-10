/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Basic
public import Quillen.Waldhausen.SConstruction
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Waldhausen K-groups from the S-construction

The space below is the realization |diag N(wS•C)|, and the nonnegative
K-groups are its shifted homotopy groups. Weak equivalences occur in the
simplices themselves. This is a definition of connective K-groups, not a
proof of additivity, comparison with Quillen Q, or localization. In
particular it does not construct the nonconnective spectrum of TT §7.
-/
@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe v u

namespace Quillen.Waldhausen

variable {C : Type u} [Category.{v} C]
variable (cof weq : MorphismProperty C)

/-- The all-zero quotient diagram is a simplex in every degree. -/
def zeroSimplex [cof.ContainsIdentities] [weq.ContainsIdentities]
    (Z : C) (hZ : IsZero Z) (n : SimplexCategoryᵒᵖ) :
    (sSet cof weq).obj n :=
  ⟨(Functor.const (Grid n.unop)).obj Z, {
    zero := fun _ _ ↦ hZ
    cofibration := fun _ _ _ _ _ _ ↦ cof.id_mem Z
    quotient := fun _ _ _ _ _ _ ↦ IsPushout.id_horiz (𝟙 Z)
    weak := fun _ _ _ _ _ _ ↦ weq.id_mem Z }⟩

/-- The genuine topological realization of the diagonal S-construction. -/
def delooping : TopCat.{max u v} := SSet.toTop.obj (sSet cof weq)

/-- The chosen zero object supplies a based vertex. -/
def basepoint [cof.ContainsIdentities] [weq.ContainsIdentities]
    (Z : C) (hZ : IsZero Z) : delooping cof weq :=
  SSet.toTop.map (SSet.yonedaEquiv.symm (zeroSimplex cof weq Z hZ (op ⦋0⦌))) default

/-- The S-construction's connective groups at a specified zero object.
This construction is available before verifying the Waldhausen axioms; the
structure-specialized `Structure.K` below records that distinction. -/
abbrev groups [cof.ContainsIdentities] [weq.ContainsIdentities]
    (Z : C) (hZ : IsZero Z) (n : ℕ) :=
  HomotopyGroup.Pi (n + 1) (delooping cof weq) (basepoint cof weq Z hZ)

namespace Structure

variable (W : Structure C)

/-- The delooping |diag N(wS•C)| of a Waldhausen category. -/
abbrev Delooping := delooping W.cof W.weq

/-- The point represented by the specified zero object. -/
abbrev kBasepoint : W.Delooping := basepoint W.cof W.weq W.zero W.isZero

/-- Waldhausen's connective K-groups. -/
abbrev K (n : ℕ) := groups W.cof W.weq W.zero W.isZero n

/-- These are actual homotopy groups, with their existing group structure. -/
example (n : ℕ) : Group (W.K n) := inferInstance

/-- Positive K-degrees are commutative by higher homotopy commutativity.
K₀ commutativity still requires the S-construction additivity theorem. -/
example (n : ℕ) : CommGroup (W.K (n + 1)) := inferInstance

end Structure

end Quillen.Waldhausen
