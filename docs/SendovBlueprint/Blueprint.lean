import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SendovBlueprint.Chapters.Main
import SendovBlueprint.Chapters.Overview
import SendovBlueprint.Chapters.Interior
import SendovBlueprint.Chapters.LowDegree
import SendovBlueprint.Chapters.Boundary
import SendovBlueprint.Chapters.FiniteRange
import SendovBlueprint.Chapters.LargeDegree

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Sendov Blueprint" =>

Blueprint for the Sendov conjecture formalization, following the blog post
[*A digestion of the proof of Sendov's conjecture*](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/)
(Terence Tao, 12 August 2026). Lemma, proposition, and equation numbers quoted
on the nodes ("Blog: Lemma 6(ii), eq. (8)") refer to that post. The chapter
[*The digested proof*](The-digested-proof/) retells the argument in the
post's order; the remaining chapters are organised by Lean module and migrated
from the plan and proof documents in `docs/`, with deviations between plan and
implementation noted on the nodes.

*History.* Sendov posed the conjecture around 1958 (it first appeared in print in
Hayman's 1967 problem collection). Rubinstein (1968) proved it for zeroes on
the unit circle, with the equality case that Phelps and Rodriguez (1972)
conjectured to be the only obstruction to a strict inequality. A sequence of
papers culminating in Brown–Xiang (1999) settled degrees $`n \le 8`, and Tao
(2020) settled all sufficiently large $`n` without an effective threshold. In
August 2026 Lech Mazur used an AI system to produce a proof for all $`n`,
verified in Lean; within days Tao digested it into the elementary argument
followed here, observed that it proves the Phelps–Rodriguez form as well, and
formalized that version in about 15,000 lines. The present blueprint documents
an independent formalization of the digested proof.

*Main results.* The principal contribution of this formalization is a complete proof of the
*Phelps–Rodriguez conjecture*, the strong form of Sendov's conjecture with
its equality case classified. Sendov's conjecture follows as a corollary.

* {bpref "main_phelps_rodriguez"}[*The Phelps–Rodriguez conjecture*]
  (`Sendov.phelps_rodriguez`): for $`n \ge 2` and $`p` of degree $`n` with all
  zeroes in the closed unit disk, every zero $`a` has a critical point $`\zeta`
  with $`|\zeta - a| < 1`, unless $`|a| = 1` and $`p = c(X^n - a^n)`.
* {bpref "main_sendov"}[*Sendov's conjecture*] (`Sendov.sendov`): the weak
  form $`|\zeta - a| \le 1`, derived directly from Phelps–Rodriguez.

The proof extends the strategy for Sendov's conjecture: the interior case
$`0 < |a| < 1` is the numerical argument
({bpref "main_stat_lt_one"}[the numerical claim for every degree], certified
degree by degree for $`5 \le n \le 100` and analytically for $`n \ge 101`),
low degrees are handled separately, and the boundary case $`|a| = 1` is
{bpref "bd_rubinstein_one"}[Rubinstein's theorem], which is where the
Phelps–Rodriguez equality case $`p = c(X^n - a^n)` comes from. Both theorems
are restated in `Solution.lean` matching `Challenge.lean`, and depend only on
the axioms `propext`, `Classical.choice`, and `Quot.sound`.

{include 0 SendovBlueprint.Chapters.Main}

{include 0 SendovBlueprint.Chapters.Overview}

{include 0 SendovBlueprint.Chapters.Interior}

{include 0 SendovBlueprint.Chapters.LowDegree}

{include 0 SendovBlueprint.Chapters.Boundary}

{include 0 SendovBlueprint.Chapters.FiniteRange}

{include 0 SendovBlueprint.Chapters.LargeDegree}

{blueprint_graph}
{blueprint_summary}
