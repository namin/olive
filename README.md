# olive: Partial Programs with Obligations

A verifier for imperative programs with **holes**. Given a partial program
with a precondition and postcondition, it produces:

- **Verification conditions** (VCs) -- logical formulas that must hold for
  the complete parts of the program.
- **Obligations** -- Hoare triples `{P} [] {Q}` specifying what any
  hole-filling must satisfy.

Obligations carry the **precise precondition** at the hole's program point
(propagated forward) and the **required postcondition** (propagated backward
via weakest precondition). VCs and obligations are checked with Z3.

See [SPEC.md](SPEC.md) for the formal rules.

Built on top of [Imp2VC2SMT](https://github.com/namin/metaprogramming/tree/master/lectures/5-smt),
a pedagogical Hoare logic verifier.

Also see implementations of Olive in:
- [Loom's Velvet](https://github.com/verse-lab/loom/compare/master...namin:loom:olive) (see [overview](https://github.com/namin/loom/blob/olive/CaseStudies/Velvet/VelvetExamples/Olive.md))
- [Dafny](https://github.com/dafny-lang/dafny/compare/master...namin:dafny:olive) (with some limitations around finding the exact pre- and post-conditions of a hole)

## Requirements

- Scala 3 (via sbt)
- [Z3](https://github.com/Z3Prover/z3) on your `PATH`

## Running

```
sbt run
```

## Language

```
c ::= skip
    | x := e
    | c1 ; c2
    | if e then c1 else c2
    | while e inv I do c
    | assert P
    | assume P
    | []           -- hole
```

Programs are annotated with a precondition and postcondition:

```scala
Program(pre, stmt, post)
```

## Example: partial max

The else branch is a hole -- what should we assign to `m` when `x >= y`?

```scala
val maxWithHole = Program(
  True,
  If(Lt(Var("x"), Var("y")),
     Assign("m", Var("y")),
     Hole(0)),
  And(Or(Eq(Var("m"), Var("x")), Eq(Var("m"), Var("y"))),
      And(Leq(Var("x"), Var("m")), Leq(Var("y"), Var("m"))))
)
```

Output:

```
Checks (2):
  [VC1]                (true => ((x < y => ...) && (!x < y => ...)))
  [OBLIGATION for []0]  {(true && !x < y)} []0 {((m = x || m = y) && ...)}
```

The obligation tells us: under `!x < y`, we need a command that establishes
the postcondition. Filling with `m := x` and re-verifying:

```scala
verifyCompletion("MaxWithHole", maxWithHole,
  Map(0 -> Assign("m", Var("x"))))
// => VERIFIED
```

Filling with `m := y` instead:

```scala
verifyCompletion("MaxWithHole (wrong)", maxWithHole,
  Map(0 -> Assign("m", Var("y"))))
// => FAILED (counterexample: x = 0, y = -1)
```

## Soundness

If all VCs are valid and every obligation `{P} [] {Q}` is discharged by the
corresponding filling, then the completed program satisfies `{pre} c' {post}`.
See SPEC.md Section 6.

## Structure

Everything is in a single file: `imp2vc2smt.scala`.

| Component | Description |
|-----------|-------------|
| AST | `AExpr`, `BExpr`, `Stmt`, `Hole(id)`, `Obligation` |
| `Verifier.wpVc` | WP + VC generation threading precondition `p` forward and postcondition `q` backward |
| `Verifier.fillHoles` | Substitute concrete commands for holes |
| `SMTLib` | Translate `BExpr` to SMT-LIB format |
| `Z3Runner` | Call Z3, parse sat/unsat/models |
| `PP` | Pretty printing |
| `Main` | Example programs, partial programs, and completions |
