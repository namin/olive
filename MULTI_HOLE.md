## Multiple Holes in Sequence

### The Setup

Consider a program with two holes in sequence and a postcondition:

```
{true} □0 ; □1 {x = 1}
```

And compare it with a variant where concrete code separates the holes:

```
{true} □0 ; x := 1 ; □1 {x = 1}
```

How does olive handle these? And does the implementation match the spec?

---

### 1. What the Spec Says

The **Sequence rule** from SPEC.md is:

```
Γ ⊢ {P} c₁ {R} ▷ O₁
Γ ⊢ {R} c₂ {Q} ▷ O₂
————————————————————————
Γ ⊢ {P} c₁ ; c₂ {Q} ▷ O₁ ∪ O₂
```

R is the **midpoint**: both the postcondition of c₁ and the precondition of c₂.
In a WP-based approach, R = wp(c₂, Q).

The **Hole rule** is:

```
———————————————
Γ ⊢ {P} □ {Q} ▷ { {P} □ {Q} }
```

A hole always produces an obligation pairing its precondition (forwarded from context) with its postcondition (from WP).

Crucially, **wp(□, Q) = Q**: the weakest precondition of a hole is just its postcondition. This is the most conservative choice — since we don't know what the hole does, we assume it needs its goal already established.

---

### 2. Consecutive Holes: `□0 ; □1`

Applying the Sequence rule to `{true} □0 ; □1 {x = 1}`:

- R = wp(□1, Q) = Q = (x = 1)
- □0 gets obligation: **{true} □0 {x = 1}** — must establish the full postcondition
- □1 gets obligation: **{x = 1} □1 {x = 1}** — must merely preserve it

This is **sound but asymmetric**: □0 does all the work, □1 is a no-op. The two holes cannot "cooperate" because the midpoint R is forced to be Q — there's no way to split the work.

The root cause: wp(□, Q) = Q means the midpoint between two consecutive holes is always the final postcondition. The first hole must reach it entirely on its own.

**Actual output:**
```
[OBLIGATION for □0]  {true} □0 {(x = 1)}
[OBLIGATION for □1]  {(x = 1)} □1 {(x = 1)}
```

The implementation matches the spec here.

---

### 3. Non-Consecutive Holes: `□0 ; x := 1 ; □1`

Now consider `{true} □0 ; (x := 1 ; □1) {x = 1}`, where c₁ = □0 and c₂ = (x := 1 ; □1).

**Per the spec**, applying the Sequence rule at the outer level:

- R = wp(c₂, Q) = wp(x := 1 ; □1, x = 1) = wp(x := 1, wp(□1, x = 1)) = wp(x := 1, x = 1) = (1 = 1) = true
- □0 gets obligation: **{true} □0 {true}** — trivially satisfied

Then for c₂ = (x := 1 ; □1) with pre R = true:

- Inner midpoint R' = wp(□1, Q) = (x = 1)
- x := 1 goes from {true} to {x = 1} — fine
- □1 gets obligation: **{x = 1} □1 {x = 1}** — also trivially satisfied by skip

So per the spec, **both obligations are trivial** — the concrete code `x := 1` does all the work.

**Actual output:**
```
[OBLIGATION for □0]  {true} □0 {(1 = 1)}
[OBLIGATION for □1]  {(1 = 1)} □1 {(x = 1)}
```

□0's obligation is trivially valid (matching the spec). But □1's obligation has precondition **(1 = 1)** instead of **(x = 1)**. The obligation `{true} □1 {x = 1}` demands that □1 establish x = 1 from scratch — even though x = 1 was *just assigned* by the preceding code.

---

### 4. The Implementation Bug

The upstream `imp2vc2smt.scala` (from the metaprogramming lectures) has no holes, so its Sequence rule is simply:

```scala
case Sequence(s1, s2) =>
  val (wp2, vcs2) = wpVc(s2, q)
  val (wp1, vcs1) = wpVc(s1, wp2)
  (wp1, vcs1 ++ vcs2)
```

No forward-flowing precondition, no bug. Olive extended this by adding a `p` parameter to thread preconditions forward to holes. The extended Sequence rule introduced a refinement step that re-runs s2 with a better precondition — but passed the wrong value:

```scala
case Sequence(s1, s2) =>
  val (wp2, vcs2, obs2) = wpVc(s2, p, q)  // wp2 = wp(s2, q) = midpoint R
  val (wp1, vcs1, obs1) = wpVc(s1, p, wp2)
  val (_, vcs2r, obs2r) = wpVc(s2, wp1, q)  // ← passes wp1 as pre for s2
  (wp1, vcs1 ++ vcs2r, obs1 ++ obs2r)
```

The comment says "the precondition for s2 is the WP of s1 (what holds after s1)". But **wp1 is the weakest precondition *before* s1**, not the state *after* s1. Specifically:

- **wp1** = wp(s1, wp2) = what must hold **before s1** for the sequence to work
- **wp2** = wp(s2, q) = the midpoint R = what holds **after s1 / before s2**

The code passes wp1 (state before s1) where the spec calls for R = wp2 (state after s1).

For hole-free programs this doesn't matter (no obligations to pollute). For consecutive holes it also doesn't matter (wp1 = wp(□, wp2) = wp2). But when concrete code appears as s1 in any sub-sequence, the WP transformation distorts the precondition.

In our example, inside c₂ = Sequence(x := 1, □1):
- wp2_inner = wp(□1, Q) = (x = 1) — the correct midpoint
- wp1_inner = wp(x := 1, (x = 1)) = (1 = 1) — the pre *before* the assignment
- The code passes wp1_inner = (1 = 1) as □1's pre, but the spec says it should be wp2_inner = (x = 1)

---

### 5. Soundness is Preserved

Despite the imprecise preconditions, the system remains **sound**. The obligation `{(1 = 1)} □1 {(x = 1)}` is *strictly harder* than the correct `{(x = 1)} □1 {(x = 1)}` — the precondition (1 = 1) is logically weaker (it's just `true`), giving the hole-filler less information to work with.

Any filling that satisfies the stricter obligation also satisfies the correct one. So the soundness theorem still holds: every accepted completion is globally correct.

What's lost is **precision**: some valid completions are rejected. In our example, `□0 → skip, □1 → skip` is a correct completion (the filled program `skip; x := 1; skip` satisfies `{true} _ {x = 1}`), but the obligation for □1 is unsatisfiable — demanding x = 1 from no information about x.

The **completion check** (which re-runs WP on the fully filled program) correctly verifies this filling. So the gap is between the obligations (too strict) and the completion check (exact).

---

### 6. The Fix

The fix (now applied) passes **wp2** (the midpoint) instead of **wp1** as the forward precondition for s2:

```scala
case Sequence(s1, s2) =>
  val (wp2, vcs2, obs2) = wpVc(s2, p, q)
  val (wp1, vcs1, obs1) = wpVc(s1, p, wp2)
  val (_, vcs2r, obs2r) = wpVc(s2, wp2, q)  // ← wp2 not wp1
  (wp1, vcs1 ++ vcs2r, obs1 ++ obs2r)
```

This gives each hole the midpoint R = wp(c₂, Q) as its forward context, matching the spec's Sequence rule exactly.

---

### 7. Deeper Limitation: Consecutive Holes Can't Cooperate

Even with the fix above, **consecutive holes remain asymmetric**. For `□0 ; □1` with post Q:

- R = wp(□1, Q) = Q
- □0: {P} □0 {Q} — must establish Q
- □1: {Q} □1 {Q} — must preserve Q

The midpoint is always Q because wp(□, Q) = Q. There's no mechanism to split the work between the two holes. This is a fundamental limitation of using WP as the sole propagation direction.

Possible extensions to address this:
- **Midpoint annotations** (like loop invariants): let the programmer supply R between holes
- **Strongest-postcondition tracking**: propagate SP forward alongside WP backward, giving holes tighter preconditions
- **Synthesis-guided splitting**: use a solver to find a midpoint R such that both obligations become satisfiable

---

### 8. Summary Table

| Program | □0 obligation | □1 obligation | Notes |
|---|---|---|---|
| `□0 ; □1` | {true} □0 {x=1} | {x=1} □1 {x=1} | □0 does all work |
| `□0 ; x:=1 ; □1` (fixed) | {true} □0 {true} | {x=1} □1 {x=1} | Both trivial; matches spec |
| `□0 ; x:=1 ; □1` (before fix) | {true} □0 {(1=1)} | {(1=1)} □1 {x=1} | □1 was too strict |
