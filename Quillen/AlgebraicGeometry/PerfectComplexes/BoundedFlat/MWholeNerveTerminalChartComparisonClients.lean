/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveTerminalChartComparison
public meta import Batteries.Tactic.Alias

/-!
# Compatibility names for the canonical terminal-chart comparison

The ten former client wrappers are direct aliases of their mathematical owner.
The original implementation is preserved in the research archive; new proofs use
`Quillen.PerfectComplexes.BassMWholeNerve.terminal_chart_comparison_*` directly.
-/

@[expose] public section

namespace Quillen.PerfectComplexes.BassMWholeNerve.TerminalComparisonClients

@[deprecated terminal_chart_comparison_zero (since := "2026-10-21")]
alias client_terminal_chart_comparison_zero := terminal_chart_comparison_zero

@[deprecated terminal_chart_comparison_one (since := "2026-10-21")]
alias client_terminal_chart_comparison_one := terminal_chart_comparison_one

@[deprecated terminal_chart_comparison_plus_one (since := "2026-10-21")]
alias client_terminal_chart_comparison_plus_one := terminal_chart_comparison_plus_one

@[deprecated terminal_chart_comparison_minus_one (since := "2026-10-21")]
alias client_terminal_chart_comparison_minus_one := terminal_chart_comparison_minus_one

@[deprecated terminal_chart_comparison_source (since := "2026-10-21")]
alias client_terminal_chart_comparison_source := terminal_chart_comparison_source

@[deprecated terminal_chart_comparison_target (since := "2026-10-21")]
alias client_terminal_chart_comparison_target := terminal_chart_comparison_target

@[deprecated terminal_chart_comparison_left (since := "2026-10-21")]
alias client_terminal_chart_comparison_left := terminal_chart_comparison_left

@[deprecated terminal_chart_comparison_right (since := "2026-10-21")]
alias client_terminal_chart_comparison_right := terminal_chart_comparison_right

@[deprecated terminal_chart_comparison_plus_laurent (since := "2026-10-21")]
alias client_terminal_chart_comparison_plus_laurent := terminal_chart_comparison_plus_laurent

@[deprecated terminal_chart_comparison_minus_laurent (since := "2026-10-21")]
alias client_terminal_chart_comparison_minus_laurent := terminal_chart_comparison_minus_laurent

end Quillen.PerfectComplexes.BassMWholeNerve.TerminalComparisonClients
