import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SendovBlueprint.Chapters.Main
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
[*A digestion of the proof of Sendov's conjecture*](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/).
Chapters are migrated from the plan and proof documents in `docs/`, with
deviations between plan and implementation noted on the nodes.

{include 0 SendovBlueprint.Chapters.Main}

{include 0 SendovBlueprint.Chapters.Interior}

{include 0 SendovBlueprint.Chapters.LowDegree}

{include 0 SendovBlueprint.Chapters.Boundary}

{include 0 SendovBlueprint.Chapters.FiniteRange}

{include 0 SendovBlueprint.Chapters.LargeDegree}

{blueprint_graph}
{blueprint_summary}
