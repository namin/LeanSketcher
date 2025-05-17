# LeanSketcher

**LeanSketcher** is an experimental Lean 4 project for automating inductive proofs and simplification. It provides lightweight custom tactics that combine structured induction, domain-specific simplification, and tactic backtracking to mimic "proof sketching."

This is a first step toward a broader system for **proof sketch automation** — blending user-supplied structure (e.g. "do induction") with tactical automation (e.g. try `grind`, `split`, `simp`, etc.).

---

## Features

* `auto_induction e`: performs induction on `e`, followed by simplification using functions in the goal and `grind`/`split` strategies.
* `auto_induction`: automatically finds an inductive hypothesis to perform induction on.
* `auto_simp`: performs `simp` using all names that appear in the goal/hypotheses.

## Repository structure

* `LeanSketcher.lean`: Main entry point for the tactics.
* `EvalOpt.lean`: Example proof script demonstrating the tactics.

---

## Acknowledgements

* Thanks to Arthur Adjedj for helping with the proofs that led to this automation.

---

## Contributing

This is an open research prototype. Contributions and experiments are welcome. Feel free to open issues for:

* new tactic ideas
* failed cases
* integration with your own proof infrastructure

---

## License

MIT
