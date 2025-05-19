# LeanSketcher

[![CI Status](https://github.com/namin/LeanSketcher/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/namin/LeanSketcher/actions/workflows/lean_action_ci.yml)


**LeanSketcher** is a nascent Lean 4 project for automating inductive proofs and simplification. It provides lightweight custom tactics that combine structured induction, domain-specific simplification, and tactic backtracking to mimic "proof sketching."

This is a first step toward a broader system for **proof sketch automation** — blending user-supplied structure (e.g. "do induction") with tactical automation (e.g. try `grind`, `split`, `simp`, etc.).

The broader system would be a discovery system, integrating learning and LLMs.

## Features

* `auto_induction e`: performs induction on `e`, followed by simplification using functions in the goal and `grind`/`split` strategies.
* `auto_induction`: automatically finds an inductive hypothesis to perform induction on.
* `auto_simp`: performs `simp` using all names that appear in the goal/hypotheses.

## Repository structure

* `LeanSketcher.lean`: Main entry point for the tactics.
* [`LeanSketcher/Basic.lean`](LeanSketcher/Basic.lean): Internals.

### Case studies

* [`EvalOpt.lean`](EvalOpt.lean): demonstrates `auto_induction` tactic, even while the tactic is just a stub.
* [`STLCInd.lean`](StlcInd.lean): manual proofs so far.

## Inspirations

* Thanks to Arthur Adjedj for helping with the proofs that led to this automation.
* Study [`grind`](https://github.com/leanprover/lean4/tree/master/src/Lean/Meta/Tactic/Grind) tactics. [Examples in the test runs prefixed with `grind_`](https://github.com/leanprover/lean4/tree/master/tests/lean/run).
* Study the textbook for [Interactive Theorem Proving at LMU SoSe 2025](https://github.com/blanchette/interactive_theorem_proving_2025). This is the best resource I found for someone familiar with Rocq.
* Study Canonical for Automated Theorem Proving in Lean ([paper](https://arxiv.org/abs/2504.06239), [code](https://github.com/chasenorman/CanonicalLean)).
* Study [cmu-l3/llmlean](https://github.com/cmu-l3/llmlean) for LLM integration from within Lean.
* Study [Aesop](https://github.com/leanprover-community/aesop) for whitebox automation.
* Study [lean-auto](https://github.com/leanprover-community/lean-auto) and [Veil](https://github.com/verse-lab/veil) for SMT integration.
