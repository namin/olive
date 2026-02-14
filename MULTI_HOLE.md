## Multiple Holes in Sequence

### 1. The Setup

Consider a program with two holes in sequence:

```
{true} □0 ; □1 {x = 1}
```

And a variant where concrete code separates the holes:

```
{true} □0 ; x := 1 ; □1 {x = 1}
```

How does olive handle these?

---

### 2. Relevant Rules

The **Sequence rule** (from SPEC.md):

```
Γ ⊢ {P} c₁ {R} ▷ O₁
Γ ⊢ {R} c₂ {Q} ▷ O₂
————————————————————————
Γ ⊢ {P} c₁ ; c₂ {Q} ▷ O₁ ∪ O₂
```

R is the **midpoint**: both the postcondition of c₁ and the precondition of c₂. In a WP-based approach, R = wp(c₂, Q).

The **Hole rule**:

```
———————————————
Γ ⊢ {P} □ {Q} ▷ { {P} □ {Q} }
```

Crucially, **wp(□, Q) = Q**: since we don't know what the hole does, we conservatively require its goal already established.

---

### 3. Consecutive Holes: `□0 ; □1`

Applying the Sequence rule to `{true} □0 ; □1 {x = 1}`:

- R = wp(□1, Q) = Q = (x = 1)
- □0 gets obligation: **{true} □0 {x = 1}** — must establish the full postcondition
- □1 gets obligation: **{x = 1} □1 {x = 1}** — must merely preserve it

**Actual output:**
```
[OBLIGATION for □0]  {true} □0 {(x = 1)}
[OBLIGATION for □1]  {(x = 1)} □1 {(x = 1)}
```

This is **sound but asymmetric**: □0 does all the work, □1 is a no-op. The two holes cannot cooperate because wp(□, Q) = Q forces the midpoint to be Q itself.

Note that the **completion check** (which re-runs WP on the fully filled program) is more precise than the obligations. The filling `□0 → x := 0, □1 → x := x + 1` violates □0's obligation (it doesn't establish x = 1), but the completed program `x := 0 ; x := x + 1` verifies correctly. Obligations are sufficient for soundness, not necessary.

---

### 4. Non-Consecutive Holes: `□0 ; x := 1 ; □1`

Now consider `{true} □0 ; (x := 1 ; □1) {x = 1}`, where c₁ = □0 and c₂ = (x := 1 ; □1).

At the outer level:

- R = wp(c₂, Q) = wp(x := 1, wp(□1, x = 1)) = wp(x := 1, x = 1) = (1 = 1) = true
- □0 gets obligation: **{true} □0 {true}** — trivially satisfied

Inside c₂ = (x := 1 ; □1) with pre R = true:

- Inner midpoint R' = wp(□1, Q) = (x = 1)
- x := 1 goes from {true} to {x = 1}
- □1 gets obligation: **{x = 1} □1 {x = 1}** — trivially satisfied by skip

**Actual output:**
```
[OBLIGATION for □0]  {true} □0 {(1 = 1)}
[OBLIGATION for □1]  {(x = 1)} □1 {(x = 1)}
```

Both obligations are valid — the concrete code `x := 1` does all the work, and the program is verified modulo obligations (`PARTIAL`). The filling `□0 → skip, □1 → skip` is correctly accepted.

---

### 5. The Asymmetry: A Fundamental Limitation

Consecutive holes are inherently asymmetric. For `□0 ; □1` with post Q:

- R = wp(□1, Q) = Q
- □0: {P} □0 {Q} — must establish Q
- □1: {Q} □1 {Q} — must preserve Q

The midpoint is always Q because wp(□, Q) = Q. There is no mechanism to split work between the holes — the first hole bears the full burden.

When concrete code separates the holes, its WP transformation can reduce the burden. In the example above, `x := 1` between the holes makes both obligations trivial. The concrete code contributes to the postcondition, relieving the holes.

---

### 6. Possible Extensions

The asymmetry could be addressed by:

- **Midpoint annotations** (like loop invariants): let the programmer supply R between consecutive holes
- **Strongest-postcondition tracking**: propagate SP forward alongside WP backward, giving holes tighter preconditions
- **Synthesis-guided splitting**: use a solver to find a midpoint R such that both obligations become satisfiable

---

### 7. Summary

| Program | □0 obligation | □1 obligation | Notes |
|---|---|---|---|
| `□0 ; □1` | {true} □0 {x=1} | {x=1} □1 {x=1} | □0 does all work |
| `□0 ; x:=1 ; □1` | {true} □0 {true} | {x=1} □1 {x=1} | Both trivial; concrete code helps |
