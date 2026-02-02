## 📜 Partial Programs with Obligations — Implementation-Agnostic Spec

### 1. 🎯 Goal

Define a small imperative calculus with:

* **partial programs** (via holes),
* a judgment that produces **obligations** from partial verification, and
* a **universal soundness theorem** over completions that discharge those obligations.

---

### 2. 🔤 Language Syntax

**Commands `c`:**

```
c ::= skip
    | x := e
    | c₁ ; c₂
    | if e then c₁ else c₂
    | while e inv I do c
    | assert P
    | assume P
    | □            // hole
```

**Expressions `e`** and predicates `P` are left abstract (assume standard).

---

### 3. 📘 Obligations

An obligation is a **Hoare triple**:

```
{P} c {Q}
```

Read: “the hole must be filled with a command that, under pre `P`, guarantees post `Q`.”

We let the **obligation set** `O` be a set of such triples.

---

### 4. 📏 Judgments

#### Full verification (standard Hoare logic):

```
Γ ⊢ {P} c {Q}
```

Only valid for hole-free programs.

#### Partial verification (our new judgment):

```
Γ ⊢ {P} c {Q} ▷ O
```

Read: "Under pre `P`, command `c` is consistent with post `Q`, producing obligations `O`."

---

### 5. 🔧 Key Rules

#### Skip

```
———————————————
Γ ⊢ {P} skip {P} ▷ ∅
```

---

#### Assignment

```
———————————————
Γ ⊢ {P[e/x]} x := e {P} ▷ ∅
```

(You can use weakest pre / substitution — classic)

---

#### Sequence

```
Γ ⊢ {P} c₁ {R} ▷ O₁
Γ ⊢ {R} c₂ {Q} ▷ O₂
————————————————————————
Γ ⊢ {P} c₁ ; c₂ {Q} ▷ O₁ ∪ O₂
```

---

#### Conditional

```
Γ ⊢ {P ∧ e} c₁ {Q} ▷ O₁
Γ ⊢ {P ∧ ¬e} c₂ {Q} ▷ O₂
————————————————————————
Γ ⊢ {P} if e then c₁ else c₂ {Q} ▷ O₁ ∪ O₂
```

---

#### While

We assume invariant `I` is supplied.

```
Γ ⊢ {I ∧ e} c {I} ▷ O₁
———————————————
Γ ⊢ {P} while e inv I do c {I ∧ ¬e} ▷ O₁ ∪ {P ⇒ I}
```

(Optionally, you can also include `I ∧ ¬e ⇒ Q` if you want to verify a follow-up command after the loop.)

---

#### Assert

```
———————————————
Γ ⊢ {P} assert P {P} ▷ ∅
```

---

#### Assume

Assume is a proof-free way to introduce obligations: we trust P.

```
———————————————
Γ ⊢ {P} assume P {true} ▷ ∅
```

---

#### Hole (crux)

```
———————————————
Γ ⊢ {P} □ {Q} ▷ { {P} □ {Q} }
```

Meaning: “for this partial step to be valid, any hole-filling must satisfy this Hoare triple.”

---

### 6. ✅ Soundness Theorem (Informal)

> If `Γ ⊢ {P} c {Q} ▷ O`,
> and `c′` is a **hole-free** completion of `c`
> such that every `{P'} □ {Q'}` ∈ O is satisfied by the corresponding part of `c′`,
> then:
>
> `Γ ⊢ {P} c′ {Q}`

This guarantees **universal soundness**: *every hole-filling that satisfies its obligation leads to global correctness.*

---

### 7. 📦 Extensions (modular / optional)

You could later add:

* Expression holes (`□_e`) with value-level obligations
* Synthesis mode (find any `c′` discharging `O`)
* Runtime checks / gradual verification fallback
* Obligation weakening / propagation


