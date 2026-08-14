# Starting a project like this one

*For someone who is new to Lean, to VS Code, to GitHub, or to coding agents — or to all four.
It describes the setup this repository actually started from, and the working habits that
turned out to matter. It is not a Lean tutorial; it is an account of how to get a formalization
project of this kind moving.*

The companion document [`making-of.md`](making-of.md) is the transcript of what followed.

---

## 1. The setup

Four things, in this order. On a reasonable laptop the whole setup is well under an hour, most
of it downloads.

**Lean.** Install via `elan`, the toolchain manager, and create a project with Mathlib as a
dependency, following the official instructions:
<https://leanprover-community.github.io/install/project.html>. Do not install Lean by hand and
do not build Mathlib from source — `lake exe cache get` downloads a prebuilt Mathlib, and the
difference is minutes against hours.

**VS Code, with the Lean 4 extension.** This is what makes Lean usable: put the cursor anywhere
in a proof and the *infoview* shows the goal at that point — what is left to prove, and what is
available to prove it with. You will read the infoview constantly, including to check what the
agent has done.

**A coding agent.** This project used [Claude Code](https://claude.com/claude-code), which runs
in the VS Code terminal (or as an extension) and can read and edit files, run `lake build`, and
read the compiler's errors.

**Git and a GitHub account.** The agent will commit for you, but the history is yours, and it is
the thing that lets you undo an afternoon that went wrong.

That is exactly how this repository started: a fresh `lake new` project, VS Code with the Lean
extension, Claude Code installed, and then a conversation.

---

## 2. What to do before writing any mathematics

Three things, all cheap, all of which paid for themselves many times over here.

**Write down what you will not accept.** In Lean, a proof can be faked in several ways: `sorry`
leaves a hole, an `axiom` assumes the thing, `native_decide` trusts a compiled binary rather
than the kernel. Decide the rules up front and put them in a script that checks them. This
project's rules are: no `sorry`, no project-defined `axiom`, no `native_decide`, no `unsafe`,
no floating point in any statement or proof. See [`../scripts/audit.sh`](../scripts/audit.sh) —
it is under sixty lines and it ran after essentially every change.

This matters more with an agent than without one. An agent under pressure to make a build pass
has a strong pull towards `sorry`, and in this project it twice reached for one and had to be
pulled back. A script that fails is a better guard than an instruction that is remembered.

**Decide what is inside the trusted base.** Anything generated outside Lean — here, Bernstein
certificates emitted by Python — should be re-verified *inside* Lean rather than believed. Get
this right at the start and a generator bug becomes a build failure instead of a false theorem.

**Make the final statement small and separate.** The thing a reader must audit is the
*statement*, not the proof. Keeping it in its own short file, importing only Mathlib and
defining nothing of its own, means someone can check what you proved without reading how. See
[`../Challenge.lean`](../Challenge.lean): 87 lines for a development of 15,000.

---

## 3. Working with the agent

**Give it a target, not a task list.** The productive messages in this project were of the form
"here is the next theorem I want, here is the informal argument, propose a plan" — not
step-by-step instructions. The agent is better at finding a route through Lean than you will be;
it is much worse than you at knowing which theorem is worth proving.

**Ask it to plan before it builds, and read the plan.** Several times the plan revealed a
misunderstanding that would have cost hours of wrong Lean.

**Ask it to check the mathematics first.** Before formalizing a chain of implications, have it
verify each one — on paper or numerically. In this project, one inequality was numerically
checked over 200,000 cases before any Lean was written, and a tempting shortcut was measured and
found to lose too much. Formalizing a false lemma is the most expensive mistake available.

**Interrupt.** You can send a message while it is working. A correction delivered mid-task is
far cheaper than one delivered after the commit. One such interruption here — "use multisets
throughout" — changed the architecture of everything downstream, for the better.

**Insist that it says when something failed.** "The build is green" and "the build is green
except for three files I stubbed out" are very different sentences. Ask for the second kind.

**Keep a design record.** A file in which the agent writes down what was decided, what was
measured, and what Lean trap it just fell into. In this project
[`design.md`](design.md) accumulated a list of Lean pitfalls that visibly stopped repeat
mistakes. It also survives the conversation: long sessions get compacted and the agent forgets,
but the file does not.

---

## 4. What to expect

**It will not be one sitting.** This project ran over four days and a long conversation that
had to be compacted several times. Commit often; the commits are what carry state across the
gaps.

**The compiler is the referee, and it is strict but honest.** A Lean proof either compiles or
it does not. This is what makes the arrangement work: you do not have to trust the agent's
assurance that a proof is correct, and neither does the agent. Everything else — is this the
right theorem, is the statement faithful, is the citation accurate — remains entirely yours.

**Expect resource problems that look like bugs.** Building many heavy files at once here
produced errors that looked exactly like disk corruption and were in fact out-of-memory. If
something inexplicable happens after a parallel build, suspect memory first. Restarting the
Lean server in VS Code (`Ctrl+Shift+P` → "Lean 4: Restart Server") clears a surprising amount.

**Expect the agent to be strongest at the middle of the difficulty range.** Routine Lean
plumbing it does far faster than a human. A genuinely novel mathematical idea it will usually
not find. The interesting zone is in between — "here is the argument, make Lean accept it" —
and that is most of a formalization.

---

## 5. If you are new to Lean specifically

You do not need to be fluent to run a project like this, but you should be able to *read* a
statement, or you cannot check what you are getting. Two things worth learning early:

- how to read a theorem statement — the hypotheses before the colon, the conclusion after;
- how to use the infoview to see the goal in the middle of a proof.

The standard entry points are
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) and the
[Natural Number Game](https://adam.math.hhu.de/). The
[Lean Zulip](https://leanprover.zulipchat.com/) is where questions get answered, usually
quickly and kindly.

A useful early exercise: take a theorem the agent has just proved, and satisfy yourself that
the *statement* says what you think it says. That skill — not the ability to write tactic
proofs — is what the arrangement in this repository actually depends on.

---

*Part of [teorth/sendov](https://github.com/teorth/sendov).*
