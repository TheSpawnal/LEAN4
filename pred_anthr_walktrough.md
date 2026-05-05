# Lean 4 Predicate Logic - Step-by-Step Walkthrough

A guided trace through `pred01` to `pred10`, designed to build intuition from
the ground up. Each proof is shown with its goal/context state evolving line
by line, mapped back to the natural deduction rules from the cheatsheet.

---

## Part 0: The Mental Model You Need First

Every Lean tactic proof is a sequence of state transformations. The state has
two halves separated by a turnstile:

```
hypothesis_name : type           <-- the CONTEXT (what you know)
another_hyp     : type
...
⊢ goal_type                      <-- the GOAL (what you must prove)
```

A tactic does one of three things:

1. **Transforms the goal**: makes it simpler, splits it, or replaces it.
   Examples: `intro`, `apply`, `constructor`, `by_cases`.
2. **Transforms the context**: derives new facts from existing ones.
   Examples: `have`, `obtain`, `cases`, `rcases`.
3. **Closes the goal**: provides the proof term directly.
   Example: `exact`.

Map this to natural deduction:

| Direction | What it looks like | Tactics |
|-----------|-------------------|---------|
| Working backward (goal-first) | "To prove G, it suffices to prove G'" | `intro`, `apply`, `constructor` |
| Working forward (context-first) | "From these facts, I derive a new one" | `have`, `obtain`, `cases` |
| Termination | "Here is the exact proof" | `exact` |

---

## Part 1: Three Pieces of Syntax to Memorize

### 1.1 Anonymous constructors `⟨ ⟩`

The angle brackets work in two directions:

**Building** (when constructing a proof of `∧`, `∃`, or `↔`):
```lean
⟨hp, hq⟩       -- builds  p ∧ q  from  hp : p  and  hq : q
⟨w, hw⟩        -- builds  ∃ x, P x  from  witness w  and  hw : P w
⟨forward, back⟩ -- builds  p ↔ q  from two implications
```

**Destructuring** (when consuming a hypothesis of `∧`, `∃`, or `↔`):
```lean
intro ⟨x, hx⟩         -- intro and immediately split an ∃ or ∧
obtain ⟨w, hw⟩ := h   -- pull h apart, naming the parts
```

`obtain` is the cleaner cousin of `cases` for `∧` and `∃`. Use `cases` (or
`rcases`) when there are multiple branches like `∨`.

### 1.2 Negation is implication in disguise

Lean **defines** `¬ A` as `A → False`. There is no separate `¬` machinery.
Consequences:

- `intro h` on a goal `¬ A` gives you `h : A` and a goal of `False`.
- If you have `hn : ¬ A` and `ha : A`, then `hn ha : False`.
- Every negation is just an implication. The tactics work the same way.

### 1.3 Universals are functions

`∀ x, P x` behaves like a function type. If `h : ∀ x, P x`, then `h a : P a`
for any `a`. No special tactic needed for elimination - it is just function
application.

For introduction: `intro x` on a goal `∀ x, P x` introduces a fresh `x` and
changes the goal to `P x`.

---

## Part 2: Walkthroughs

### pred01

```lean
theorem pred01 : (∀ x, ∀ y, R x y) → ∀ x, R x x := by
  intro h x
  exact h x x
```

**English**: if R holds between every pair, then R holds reflexively.

**Initial state:**
```
⊢ (∀ x, ∀ y, R x y) → ∀ x, R x x
```

**Step 1: `intro h x`**

This is two intros chained. The first peels off the implication; the second
peels off the outer `∀` of the conclusion.

State after:
```
h : ∀ x, ∀ y, R x y
x : Prop
⊢ R x x
```

ND mapping: `→I` (cheatsheet Implication section), then `∀I` (Quantifiers).

**Step 2: `exact h x x`**

`h` is a "two-argument function". Apply it to `x` once to get `∀ y, R x y`,
again to get `R x x`. Two `∀E` steps inlined as function application.

**Key intuition**: `intro` can take multiple names at once. Each name handles
one outer connective from left to right.

---

### pred02

```lean
theorem pred02 (h : ∀ x, Q x) : (∃ x, Q x → P x) → ∃ x, P x := by
  intro ⟨x, hx⟩
  exact ⟨x, hx (h x)⟩
```

**English**: given that everything has Q, and that some element has the
property "Q implies P", we can produce something that has P.

**Initial state:**
```
h : ∀ x, Q x
⊢ (∃ x, Q x → P x) → ∃ x, P x
```

**Step 1: `intro ⟨x, hx⟩`**

This does **two things in one stroke**: it intros the antecedent of the
implication, then immediately destructures the resulting existential. Without
the shortcut you would write:
```lean
intro hex
obtain ⟨x, hx⟩ := hex
```

State after:
```
h  : ∀ x, Q x
x  : Prop
hx : Q x → P x
⊢ ∃ x, P x
```

ND mapping: `→I` then `∃E`.

**Step 2: `exact ⟨x, hx (h x)⟩`**

Building the goal:
- Witness: `x`.
- Proof of `P x`: `h x` gives `Q x` (by `∀E`), then `hx (h x)` gives `P x`
  (by `→E`).

ND mapping: `∀E`, `→E`, then `∃I`.

**Key intuition**: anonymous constructors can be built directly inside
`exact`. You do not need to state the witness with `apply Exists.intro` first.

---

### pred03

```lean
theorem pred03 (h : ∃ x, ∀ y, P y x) : ∀ x, ∃ y, P x y := by
  obtain ⟨a, ha⟩ := h
  intro x
  exact ⟨a, ha x⟩
```

**English**: if some element `a` is "universally targeted" (everything relates
to it via P), then for every x there is something it relates to (namely `a`).

This is the easy direction; the converse is **not** provable. Notice that the
existence in the conclusion is dependent on `x` in general, but here we get
away with using the same `a` for every `x`.

**Initial state:**
```
h : ∃ x, ∀ y, P y x
⊢ ∀ x, ∃ y, P x y
```

**Step 1: `obtain ⟨a, ha⟩ := h`**

Forward reasoning. We extract the witness from `h`. Note: the bound variable
in `h` was named `x`, but that name was internal - we rename the witness `a`
to avoid colliding with the `x` we will introduce next.

State after:
```
a  : Prop
ha : ∀ y, P y a
⊢ ∀ x, ∃ y, P x y
```

ND mapping: `∃E`.

**Step 2: `intro x`**

Backward reasoning on the goal.

State after:
```
a  : Prop
ha : ∀ y, P y a
x  : Prop
⊢ ∃ y, P x y
```

ND mapping: `∀I`.

**Step 3: `exact ⟨a, ha x⟩`**

Witness: `a`. Body: `ha x : P x a`, which matches `P x y[y := a]`.

**Key intuition**: when you have an `∃` and a `∀` to deal with, **destructure
the `∃` first** so its witness is in scope when you intro the `∀`. The other
order also works but is clumsier.

---

### pred04

```lean
theorem pred04 : (∀ x, ¬ P x) → ¬ ∃ x, P x := by
  intro h ⟨x, hx⟩
  exact h x hx
```

**English**: classic De Morgan-style law. If nothing has P, there does not
exist anything with P.

**Initial state:**
```
⊢ (∀ x, ¬ P x) → ¬ ∃ x, P x
```

Remember: `¬ ∃ x, P x` unfolds to `(∃ x, P x) → False`. So the whole goal
is really:
```
(∀ x, ¬ P x) → (∃ x, P x) → False
```

**Step 1: `intro h ⟨x, hx⟩`**

Three things in one:
1. Intro the outer implication antecedent: `h : ∀ x, ¬ P x`.
2. Intro the (unfolded) negation antecedent: an `∃ x, P x`.
3. Destructure that existential into `x` and `hx`.

State after:
```
h  : ∀ x, ¬ P x
x  : Prop
hx : P x
⊢ False
```

**Step 2: `exact h x hx`**

`h x : ¬ P x`, which is `P x → False`. Apply to `hx : P x` to get `False`.

**Key intuition**: when you see `¬ ∃` in a goal, mentally rewrite it as
`(∃ ...) → False`. Then `intro` works exactly as you expect.

---

### pred05

```lean
theorem pred05 : (∀ x, P x) → ¬ ∃ x, ¬ P x := by
  intro h ⟨x, hnx⟩
  exact hnx (h x)
```

**English**: same flavour as pred04. If everything has P, there can be no
counterexample.

**Initial state:**
```
⊢ (∀ x, P x) → ¬ ∃ x, ¬ P x
```

**Step 1: `intro h ⟨x, hnx⟩`**

Same triple-action as pred04.

State after:
```
h   : ∀ x, P x
x   : Prop
hnx : ¬ P x
⊢ False
```

**Step 2: `exact hnx (h x)`**

`h x : P x`. `hnx : P x → False`. Apply to get `False`.

**Key intuition**: when the goal is `False` and you have a `¬ A` and an `A`,
just apply the `¬` to the `A`. That is the only thing you can do.

---

### pred06

```lean
theorem pred06 (h : ∃ x, Q x) : ¬ ∀ x, P x ∧ ¬ ∃ y, P y := by
  obtain ⟨w, _⟩ := h
  intro hall
  obtain ⟨hPw, hnex⟩ := hall w
  exact hnex ⟨w, hPw⟩
```

**English**: it is impossible for every `x` to simultaneously have `P` while
also denying that any `y` has `P`. The body of the universal is
self-contradictory.

**Parsing note**: `∀ x, P x ∧ ¬ ∃ y, P y` reads as
`∀ x, (P x ∧ ¬ (∃ y, P y))`. Quantifiers reach as far right as they can.

**Initial state:**
```
h : ∃ x, Q x
⊢ ¬ ∀ x, P x ∧ ¬ ∃ y, P y
```

**Step 1: `obtain ⟨w, _⟩ := h`**

Get a witness `w`. We don't care about `Q w` (the underscore tells Lean to
discard it). We just need *something* of the right type.

State after:
```
w : Prop
⊢ ¬ ∀ x, P x ∧ ¬ ∃ y, P y
```

**Step 2: `intro hall`**

The goal is a negation, so intro turns it into a contradiction goal.

State after:
```
w    : Prop
hall : ∀ x, P x ∧ ¬ ∃ y, P y
⊢ False
```

**Step 3: `obtain ⟨hPw, hnex⟩ := hall w`**

Specialize the universal at `w` (`∀E`), then split the resulting `∧`.

State after:
```
hPw  : P w
hnex : ¬ ∃ y, P y
⊢ False
```

**Step 4: `exact hnex ⟨w, hPw⟩`**

Build `∃ y, P y` from witness `w` and proof `hPw`. Then `hnex` (which is
`(∃ y, P y) → False`) refutes it.

**Key intuition**: when a universal is in the context and you want to use it,
specialize it at a concrete element. The element often comes from another
existential elsewhere.

---

### pred07 (Barber Paradox)

```lean
theorem pred07 : ¬ ∀ (x : Person), shaves barber x ↔ ¬ shaves x x := by
  intro h
  have h_barber := h barber
  by_cases h_shaves : shaves barber barber
  · have h_not_shaves := h_barber.mp h_shaves
    exact h_not_shaves h_shaves
  · have h_shaves_again := h_barber.mpr h_shaves
    exact h_shaves h_shaves_again
```

**English**: there cannot exist a barber who shaves all and only those who
do not shave themselves. The classical Russell-flavoured paradox.

**Initial state:**
```
⊢ ¬ ∀ x, shaves barber x ↔ ¬ shaves x x
```

**Step 1: `intro h`**

State after:
```
h : ∀ x, shaves barber x ↔ ¬ shaves x x
⊢ False
```

**Step 2: `have h_barber := h barber`**

Specialize the universal at the barber himself. `have` writes the result into
the context.

State after:
```
h         : ∀ x, ...
h_barber  : shaves barber barber ↔ ¬ shaves barber barber
⊢ False
```

This is `A ↔ ¬ A` - the canonical self-referential contradiction.

**Step 3: `by_cases h_shaves : shaves barber barber`**

Splits the proof into two parallel universes via the law of excluded middle.

**Branch 1** (`h_shaves : shaves barber barber`):
- `h_barber.mp` is `shaves barber barber → ¬ shaves barber barber`
  (the forward direction of `↔`, which is `Iff.mp` in the cheatsheet).
- `h_barber.mp h_shaves : ¬ shaves barber barber`.
- Apply that to `h_shaves` to get `False`.

**Branch 2** (`h_shaves : ¬ shaves barber barber`):
- `h_barber.mpr` is `¬ shaves barber barber → shaves barber barber`.
- `h_barber.mpr h_shaves : shaves barber barber`.
- Now `h_shaves` (the negation) applied to that fact gives `False`.

**Stylistic note**: this proof uses `by_cases` (classical), but the Barber
paradox is actually provable **constructively**. The commented-out version
in your file shows how:
```lean
intro h
obtain ⟨mp, mpr⟩ := h barber
have hn : ¬ shaves barber barber := fun hs => mp hs hs
exact hn (mpr hn)
```
The trick: build `¬ shaves barber barber` directly (assume `hs`, use `mp` to
turn it into a `¬`, then apply that `¬` to `hs`). Then feed that `¬` into
`mpr` to recover the affirmative, and refute it.

If your course is strict about staying in the constructive fragment of the
cheatsheet, prefer the commented version. The classical version is fine and
easier to read for beginners.

**Key intuition**: when you have an iff in context, `.mp` and `.mpr` give you
the two implication directions. They are just function application, not
tactics.

---

### pred08 (Drinker-style theorem)

```lean
theorem pred08 (h1 : P → ∃ x, Q x) (h2 : ∃ x, R x) : ∃ x, P → Q x := by
  obtain ⟨w, _⟩ := h2
  by_cases hp : P
  · obtain ⟨x, hx⟩ := h1 hp
    exact ⟨x, fun _ => hx⟩
  · exact ⟨w, fun hp' => absurd hp' hp⟩
```

**English**: there exists some element such that "P implies Q of that
element". The hypothesis `h2` is needed only to guarantee the universe is
nonempty.

This **genuinely requires classical logic**. The pure constructive version
is unprovable in general - you cannot point to a specific witness without
knowing whether `P` holds.

**Initial state:**
```
h1 : P → ∃ x, Q x
h2 : ∃ x, R x
⊢ ∃ x, P → Q x
```

**Step 1: `obtain ⟨w, _⟩ := h2`**

Pull out a witness from the nonemptiness assumption. We don't need `R w`
(hence the underscore), just *some* element to point at if needed.

State after:
```
h1 : P → ∃ x, Q x
w  : Prop
⊢ ∃ x, P → Q x
```

**Step 2: `by_cases hp : P`**

Classical case split: either `P` holds or it doesn't.

**Branch 1** (`hp : P`):
```lean
obtain ⟨x, hx⟩ := h1 hp
exact ⟨x, fun _ => hx⟩
```
- `h1 hp : ∃ x, Q x`. Destructure to get `x : Prop` and `hx : Q x`.
- Build the goal with witness `x`. The proof term `fun _ => hx` is an
  implication that ignores its input and just returns `hx`. The implication's
  premise is `P`, which is satisfied vacuously since `Q x` is already known.

**Branch 2** (`hp : ¬ P`):
```lean
exact ⟨w, fun hp' => absurd hp' hp⟩
```
- Witness: `w` (the only thing we have).
- Body: given some `hp' : P`, we have `hp : ¬ P`. `absurd hp' hp` produces a
  proof of *anything* (in particular `Q w`) by ex falso. The implication is
  vacuously true because its premise is impossible.

**Key intuition**: when the goal is `∃ x, ...` involving an implication body,
think about what makes the implication true:
1. its conclusion is true regardless (use the witness from there), or
2. its premise is false (witness can be anything, conclusion vacuous).
Classical logic lets you decide which case applies via `by_cases`.

---

### pred09

```lean
theorem pred09 (h : ∀ x, R x → P x) : (∀ x, Q x ∧ R x) → ∀ x, P x ∧ Q x := by
  intro hall x
  obtain ⟨hQx, hRx⟩ := hall x
  exact ⟨h x hRx, hQx⟩
```

**English**: if `R` always implies `P`, then "everything has Q and R" implies
"everything has P and Q". Just plumbing.

**Initial state:**
```
h : ∀ x, R x → P x
⊢ (∀ x, Q x ∧ R x) → ∀ x, P x ∧ Q x
```

**Step 1: `intro hall x`**

Two intros: the implication antecedent, then the universal binder.

State after:
```
h    : ∀ x, R x → P x
hall : ∀ x, Q x ∧ R x
x    : Prop
⊢ P x ∧ Q x
```

**Step 2: `obtain ⟨hQx, hRx⟩ := hall x`**

Specialize `hall` at `x`, then split the conjunction.

State after:
```
hQx : Q x
hRx : R x
⊢ P x ∧ Q x
```

**Step 3: `exact ⟨h x hRx, hQx⟩`**

Build `P x ∧ Q x`:
- Left part: `h x : R x → P x`, applied to `hRx`, gives `P x`.
- Right part: `hQx : Q x` directly.

**Key intuition**: most "shuffle the parts" proofs collapse into a single
`exact ⟨..., ...⟩` after a couple of intros and one obtain.

---

### pred10

```lean
theorem pred10 (h : ∀ x, (∃ y, P x y) ∨ (∀ y, ¬ P y x)) :
    ∀ x, ∃ y, ∀ z, P x y ∨ ¬ P z y := by
  intro x
  rcases h x with ⟨y, hPxy⟩ | hneg
  · exact ⟨y, fun _ => Or.inl hPxy⟩
  · exact ⟨x, fun z => Or.inr (hneg z)⟩
```

**English**: for every `x`, we can pick a `y` such that for any third element
`z`, either `P x y` holds, or `P z y` fails. The choice of `y` depends on
which side of the disjunction holds for our chosen `x`.

This is the most involved proof. Take it slowly.

**Initial state:**
```
h : ∀ x, (∃ y, P x y) ∨ (∀ y, ¬ P y x)
⊢ ∀ x, ∃ y, ∀ z, P x y ∨ ¬ P z y
```

**Step 1: `intro x`**

State after:
```
h : ∀ x, (∃ y, P x y) ∨ (∀ y, ¬ P y x)
x : Prop
⊢ ∃ y, ∀ z, P x y ∨ ¬ P z y
```

**Step 2: `rcases h x with ⟨y, hPxy⟩ | hneg`**

`rcases` is the heavyweight version of `cases` that supports nested patterns.
Here `h x` is a disjunction. The pipe `|` separates the two `∨` branches:
- Left: an existential, destructured into `y` and `hPxy : P x y`.
- Right: kept whole as `hneg : ∀ y, ¬ P y x`.

**Branch 1** (left, the easy case):
```
y    : Prop
hPxy : P x y
⊢ ∃ y, ∀ z, P x y ∨ ¬ P z y
```

`exact ⟨y, fun _ => Or.inl hPxy⟩`:
- Witness: `y` (from the existential we destructured).
- Body: the goal is `∀ z, P x y ∨ ¬ P z y`. Take `fun _ => ...` (a function
  ignoring its input) returning `Or.inl hPxy`, which picks the left disjunct.

ND mapping: `∃E` (already done by `rcases`), `∃I`, `∀I`, `∨IL`.

**Branch 2** (right, the clever case):
```
hneg : ∀ y, ¬ P y x
⊢ ∃ y, ∀ z, P x y ∨ ¬ P z y
```

`exact ⟨x, fun z => Or.inr (hneg z)⟩`:
- Witness: **`x` itself** - this is the trick. Why? Because then the goal
  body becomes `∀ z, P x x ∨ ¬ P z x`, and `hneg z : ¬ P z x` can prove the
  right disjunct directly.
- Body: given `z`, return `Or.inr (hneg z)`.

ND mapping: `∃I` with the witness, `∀I`, `∀E` on `hneg`, `∨IR`.

**Why does picking `y := x` work?** The right disjunct of `h` says "for all
`y`, `¬ P y x`". The conclusion's right disjunct of the inner `∨` is
`¬ P z y`. If we pick `y := x` in the conclusion, it becomes `¬ P z x`,
and `hneg z` is exactly that. The witness has to align with the second
argument of `P` in `hneg`.

**Key intuition**: when an existential has nested universals, the witness
choice matters and is often forced by what hypothesis you can apply. Trace
the types backward from `hneg z` to figure out what witness makes them line
up.

---

## Part 3: Pattern Library

Things you will reach for repeatedly:

| Pattern | Tactic |
|---------|--------|
| Goal is `A → B` | `intro h` |
| Goal is `∀ x, P x` | `intro x` |
| Goal is `¬ A` | `intro h` (then prove `False`) |
| Goal is `A ∧ B` | `exact ⟨proof_of_A, proof_of_B⟩` |
| Goal is `∃ x, P x` | `exact ⟨witness, proof⟩` |
| Goal is `A ∨ B`, want left | `exact Or.inl (...)` |
| Goal is `A ∨ B`, want right | `exact Or.inr (...)` |
| Have `h : A ∧ B` | `obtain ⟨ha, hb⟩ := h` |
| Have `h : ∃ x, P x` | `obtain ⟨w, hw⟩ := h` |
| Have `h : A ∨ B` | `rcases h with ha \| hb` |
| Have `h : A ↔ B` | use `h.mp` and `h.mpr` directly |
| Have `h : ∀ x, P x`, want `P a` | just write `h a` |
| Have `h : A → B` and `ha : A` | just write `h ha` |
| Need classical case split | `by_cases hp : P` |

The single biggest leap from natural deduction to Lean is realizing that
**most elimination rules are just function application**. You do not need a
tactic to "use" a hypothesis of type `A → B` or `∀ x, P x` - you just apply
it like a function.

---

## Part 4: Common Beginner Pitfalls

1. **Forgetting that `¬ A = A → False`**. When you see a `¬` in a goal or
   context, mentally unfold it. The same tactics work.

2. **Using `cases` for `∧` and `∃`**. It works, but `obtain ⟨...⟩ := h` is
   cleaner. Save `cases` for when you genuinely have multiple branches
   (`∨`, inductive types).

3. **Trying to "prove" an `∃` without picking a witness**. Lean is
   constructive by default. You must say `⟨w, ...⟩` and provide `w`
   explicitly. The only way out is classical reasoning, which is more work.

4. **Wrong order of `intro` and `obtain` for mixed `∃`/`∀`**. If you have
   `(∃ x, ...) → ∀ y, ...`, you usually want to intro the implication, then
   destructure the `∃`, then intro the `∀`. Choose the order that puts the
   most information into the context before each goal step.

5. **Picking the wrong witness for a tricky `∃`**. As in pred10, the right
   witness is determined by what hypothesis you can use to close the goal.
   Work backward from the goal types to figure out what value makes them
   match.

---

## Part 5: A Recommended Reading Order

If you are revisiting these later to test your intuition without looking at
the proofs:

1. **pred01, pred05, pred09** - basic plumbing. Build muscle memory for
   `intro`, `obtain`, and `exact ⟨...⟩`.
2. **pred02, pred04** - mixing `→` with `∃`. Get comfortable with the
   `intro ⟨x, hx⟩` shortcut.
3. **pred03, pred06** - using `∀E` (function application) and witnessing
   strategy.
4. **pred07** - iff-handling and the Russell pattern.
5. **pred08** - classical reasoning with `by_cases`.
6. **pred10** - witness selection driven by hypothesis matching.
