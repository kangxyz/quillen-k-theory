/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.VectorBundleInclusion
public import Quillen.AlgebraicGeometry.PerfectComplexes.Restriction
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalLifting
public import Quillen.AlgebraicGeometry.PerfectComplexes.Support
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Closure
public import Quillen.AlgebraicGeometry.PerfectComplexes.PerfectSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.SplitSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.SplitComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.QuillenComparison

/-!
# Public strict and locally-perfect connective K-theory

This interface exposes canonical maps from public scheme K, the actual
quasi-isomorphism Waldhausen S-construction,
strict and locally-perfect K-groups with their actual support/restriction maps,
and the genuinely local perfectness predicate in the actual derived localization.
Both ambient-monomorphism and degreewise-split cofibration models, with
perfect quotient, are provided, and their canonical comparison maps are proved
to be equivalences in every nonnegative degree. It does not identify
strict-perfect K with all-perfect K or with the existing vector-bundle Q model.
Those comparison and localization theorems require separate proofs.
-/
@[expose] public section
