import NngLocal.Worlds.W04_Power
import NngLocal.MyNat.Definition
import NngLocal.MyNat.PeanoAxioms
import NngLocal.Tactic.Cases
import NngLocal.Tactic.FromMathlib
import NngLocal.Tactic.Induction
import NngLocal.Tactic.Ne
import NngLocal.Tactic.Rfl
import NngLocal.Tactic.Rw
import NngLocal.Tactic.SimpAdd
import NngLocal.Tactic.Use

/-! # Implication World

We've proved that $2+2=4$; in Implication World we'll learn
how to prove $2+2\neq 5$.

In Addition World we proved *equalities* like $x + y = y + x$.
In this second tutorial world we'll learn some new tactics,
enabling us to prove *implications*
like $x+1=4 \implies x=3.$

We'll also learn two new fundamental facts about
natural numbers, which Peano introduced as axioms.

Click on "Start" to proceed.

Extracted from NNG4 `Game/Levels/Implication`. Replace each `sorry` with a proof.
-/

namespace MyNat

/-! ## Level 1 · The `exact` tactic

In this world we'll learn how to prove theorems of the form $P\implies Q$.
In other words, how to prove theorems of the form "if $P$ is true, then $Q$ is true."
To do that we need to learn some more tactics.

The `exact` tactic can be used to close a goal which is exactly one of
the hypotheses. It takes the name of the hypothesis as argument: `exact h`.

### Tactic `exact`

## Summary

If the goal is a statement `P`, then `exact h` will close the goal if `h` is a proof of `P`.

### Example

If the goal is `x = 37` and you have a hypothesis `h : x = 37`
then `exact h` will solve the goal.

### Example

If the goal is `x + 0 = x` then `exact add_zero x` will close the goal.

### Exact needs to be exactly right

Note that `exact add_zero` will *not work* in the previous example;
for `exact h` to work, `h` has to be *exactly* a proof of the goal.
`add_zero` is a proof of `∀ n, n + 0 = n` or, if you like,
a proof of `? + 0 = ?` where `?` needs to be supplied by the user.
This is in contrast to `rw` and `apply`, which will \"guess the inputs\"
if necessary. If the goal is `x + 0 = x` then `rw [add_zero]`
and `rw [add_zero x]` will both change the goal to `x = x`,
because `rw` guesses the input to the function `add_zero`.
-/

/- Assuming $x+y=37$ and $3x+z=42$, we have $x+y=37$. -/
set_option linter.unusedVariables false in
example (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  -- Hint: The goal in this level is one of our hypotheses. Solve the goal by executing `exact h1`.
  sorry


/-! ## Level 2 · `exact` practice.

If the goal is not *exactly* a hypothesis, we can sometimes
use rewrites to fix things up.
-/

/- Assuming $0+x=(0+y)+2$, we have $x=y+2$. -/
example (x y : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- Hint: You can use `rw [zero_add] at {h}` to rewrite at `{h}` instead
  --     of at the goal.
  -- Hint (hidden): Do that again!
  --
  --     `rw [zero_add] at {h}` tries to fill in
  --     the arguments to `zero_add` (finding `{x}`) then it replaces all occurrences of
  --     `0 + {x}` it finds. Therefore, it did not rewrite `0 + {y}`, yet.
  -- Hint: Now you could finish with `rw [{h}]` then `rfl`, but `exact {h}`
  --     does it in one line.
  sorry


/-! **Conclusion.** Here's a two-line proof:
```
repeat rw [zero_add] at h
exact h
``` -/

/-! ## Level 3 · The `apply` tactic.

In this level, the hypothesis `h2` is an *implication*. It says
that *if* `x = 37` *then* `y = 42`. We can use this
hypothesis with the `apply` tactic. Remember you can click on
`apply` or any other tactic on the right to see a detailed explanation
of what it does, with examples.

### Tactic `apply`

## Summary

If `t : P → Q` is a proof that $P \implies Q$, and `h : P` is a proof of `P`,
then `apply t at h` will change `h` to a proof of `Q`. The idea is that if
you know `P` is true, then you can deduce from `t` that `Q` is true.

If the *goal* is `Q`, then `apply t` will \"argue backwards\" and change the
goal to `P`. The idea here is that if you want to prove `Q`, then by `t`
it suffices to prove `P`, so you can reduce the goal to proving `P`.

### Example:

`succ_inj x y` is a proof that `succ x = succ y → x = y`.

So if you have a hypothesis `h : succ (a + 37) = succ (b + 42)`
then `apply succ_inj at h` will change `h` to `a + 37 = b + 42`.
You could write `apply succ_inj (a + 37) (b + 42) at h`
but Lean is smart enough to figure out the inputs to `succ_inj`.

### Example

If the goal is `a * b = 7`, then `apply succ_inj` will turn the
goal into `succ (a * b) = succ 7`.
-/

/- If $x=37$ and we know that $x=37\implies y=42$ then we can deduce $y=42$. -/
example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  -- Hint: Start with `apply h2 at h1`. This will change `h1` to `y = 42`.
  -- Hint: Now finish using the `exact` tactic.
  sorry


/-! ## Level 4 · succ_inj : the successor function is injective

If `a` and `b` are numbers, then `succ_inj a b` is a proof
that `succ a = succ b` implies `a = b`. Click on this theorem in the *Peano*
tab for more information.

Peano had this theorem as an axiom, but in Algorithm World
we will show how to prove it in Lean. Right now let's just assume it,
and let's prove $x+1=4 \implies x=3$ using it. Again, we will proceed
by manipulating our hypothesis until it becomes the goal. I will
walk you through this level.

### New theorems

* `succ_inj` — # Statement If $a$ and $b$ are numbers, then `succ_inj a b` is the proof that $ (\operatorname{succ}(a) = \operatorname{succ}(b)) \implies a=b$. ## More technical details There are other ways to think about `succ_inj`. You can think about `succ_inj` itself as a function which takes two numbers $$a$$ and $$b$$ as input, and outputs a proof of $ ( \operatorname{succ}(a) = \operatorname{succ}(b)) \implies a=b$. You can think of `succ_inj` itself as a proof; it is the proof that `succ` is an injective function. In other words, `succ_inj` is a proof of $\forall a, b \in \mathbb{N}, ( \operatorname{succ}(a) = \operatorname{succ}(b)) \implies a=b$. `succ_inj` was postulated as an axiom by Peano, but in Lean it can be proved using `pred`, a mathematically pathological function.
-/

/- If $x+1=4$ then $x=3$. -/
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- Hint: Let's first get `h` into the form `succ x = succ 3` so we can
  --     apply `succ_inj`. First execute `rw [four_eq_succ_three] at h`
  --     to change the 4 on the right hand side.
  -- Hint: Now rewrite `succ_eq_add_one` backwards at `h`
  --     to get the right hand side.
  -- Hint: You can put a `←` in front of any theorem provided to `rw` to rewrite
  --     the other way around. Look at the docs for `rw` for an explanation. Type `←` with `\l`.
  -- Hint (hidden): Concretely: `rw [← succ_eq_add_one] at h`.
  -- Hint: Now let's `apply` our new theorem. Execute `apply succ_inj at h`
  --     to change `h` to a proof of `x = 3`.
  -- Hint: Now finish in one line.
  -- Hint (hidden): And now we've deduced what we wanted to prove: the goal is one of our assumptions.
  --     Finish the level with `exact h`.
  sorry


/-! **Conclusion.** In the next level, we'll do the same proof but backwards. -/

/-! ## Level 5 · Arguing backwards

In the last level, we manipulated the hypothesis `x + 1 = 4`
  until it became the goal `x = 3`. In this level we'll manipulate
  the goal until it becomes our hypothesis! In other words, we
  will "argue backwards". The `apply` tactic can do this too.
  Again I will walk you through this one (assuming you're in
  "Typewriter mode").
-/

/- If $x+1=4$ then $x=3$. -/
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- Hint: Start with `apply succ_inj` to apply `succ_inj` to the *goal*.
  -- Hint: Applying a proof of $P\implies Q$ to the *goal* changes $Q$ to $P$.
  --     Now try `rw [succ_eq_add_one]` to make the goal more like the hypothesis.
  -- Hint: Now rewrite `four_eq_succ_three` backwards to make the goal
  --     equal to the hypothesis.
  -- Hint: You can now finish with `exact h`.
  sorry


/-! **Conclusion.** Many people find `apply t at h` easy, but some find `apply t` confusing.
If you find it confusing, then just argue forwards.

You can read more about the `apply` tactic in its documentation, which you can view by
clicking on the tactic in the list on the right. -/

/-! ## Level 6 · intro

We have seen how to `apply` theorems and assumptions
of the form `P → Q`. But what if our *goal* is of the form `P → Q`?
To prove this goal, we need to know how to say "let's assume `P` and deduce `Q`".
In Lean, we do this with the `intro` tactic.

### Tactic `intro`

## Summary

If the goal is `P → Q`, then `intro h` will introduce `h : P` as a hypothesis,
and change the goal to `Q`. Mathematically, it says that to prove $P \implies Q$,
we can assume $P$ and then prove $Q$.

### Example:

If your goal is `x + 1 = y + 1 → x = y` (the way Lean writes $x+1=y+1 \implies x=y$)
then `intro h` will give you a hypothesis $x+1=y+1$ named `h`, and the goal
will change to $x=y$.
-/

/- $x=37\implies x=37$. -/
example (x : ℕ) : x = 37 → x = 37 := by
  -- Hint: Start with `intro h` to assume the hypothesis and call its proof `h`.
  -- Hint (hidden): Now `exact h` finishes the job.
  sorry


/-! ## Level 7 · intro practice

Let's see if you can use the tactics we've learnt to prove $x+1=y+1\implies x=y$.
Try this one by yourself; if you need help then click on "Show more help!".
-/

/- $x+1=y+1 \implies x=y$. -/
example (x y : ℕ) : x + 1 = y + 1 → x = y := by
  -- Hint (hidden): Start with `intro h` to assume the hypothesis.
  -- Hint (hidden): Now `repeat rw [← succ_eq_add_one] at h` is the quickest way to
  --     change `h` to `succ x = succ y`.
  -- Hint (hidden): Now `apply succ_inj at h` to cancel the `succ`s.
  -- Hint (hidden): Now `rw [h]` then `rfl` works, but `exact h` is quicker.
  sorry


/-! **Conclusion.** Here's a completely backwards proof:
```
intro h
apply succ_inj
repeat rw [succ_eq_add_one]
exact h
``` -/

/-! ## Level 8 · ≠

We still can't prove `2 + 2 ≠ 5` because we have not talked about the
definition of `≠`. In Lean, `a ≠ b` is *notation* for `a = b → False`.
Here `False` is a generic false proposition, and `→` is Lean's notation
for "implies". In logic we learn
that `True → False` is false, but `False → False` is true. Hence
`X → False` is the logical opposite of `X`.

Even though `a ≠ b` does not look like an implication,
you should treat it as an implication. The next two levels will show you how.

`False` is a goal which you cannot deduce from a consistent set of assumptions!
So if your goal is `False` then you had better hope that your hypotheses
are contradictory, which they are in this level.
-/

/- If $x=y$ and $x \neq y$ then we can deduce a contradiction. -/
example (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  -- Hint: Remember that `h2` is a proof of `x = y → False`. Try
  --     `apply`ing `h2` either `at h1` or directly to the goal.
  sorry


/-! **Conclusion.** Remember, `x ≠ y` is *notation* for `x = y → False`. -/

/-! ## Level 9 · zero_ne_succ

As warm-up for `2 + 2 ≠ 5` let's prove `0 ≠ 1`. To do this we need to
introduce Peano's last axiom `zero_ne_succ n`, a proof that `0 ≠ succ n`.
To learn about this result, click on it in the list of lemmas on the right.

### New theorems

* `zero_ne_succ` — `zero_ne_succ n` is the proof that `0 ≠ succ n`. In Lean, `a ≠ b` is *defined to mean* `a = b → False`. Hence `zero_ne_succ n` is really a proof of `0 = succ n → False`. Here `False` is a generic false statement. This means that you can `apply zero_ne_succ at h` if `h` is a proof of `0 = succ n`.
-/

/-- $0\neq1$. -/
theorem zero_ne_one: (0 : ℕ) ≠ 1 := by
  -- Hint: Start with `intro h`.
  -- Hint: Now change `1` to `succ 0` in `h`.
  -- Hint: Now you can `apply zero_ne_succ at h`.
  sorry


/-! **Conclusion.** Nice! -/

/-! ## Level 10 · 1 ≠ 0

We know `zero_ne_succ n` is a proof of `0 = succ n → False` -- but what
if we have a hypothesis `succ n = 0`? It's the wrong way around!

The `symm` tactic changes a goal `x = y` to `y = x`, and a goal `x ≠ y`
to `y ≠ x`. And `symm at h`
does the same for a hypothesis `h`. We've proved $0 \neq 1$ and called
the proof `zero_ne_one`; now try proving $1 \neq 0$.

### Tactic `symm`

## Summary

The `symm` tactic will change a goal or hypothesis of
the form `X = Y` to `Y = X`. It will also work on `X ≠ Y`
and on `X ↔ Y`.

### Example

If the goal is `2 + 2 = 4` then `symm` will change it to `4 = 2 + 2`.

### Example

If `h : 2 + 2 ≠ 5` then `symm at h` will change `h` to `5 ≠ 2 + 2`.
-/

/-- $1\neq0$. -/
theorem one_ne_zero: (1 : ℕ) ≠ 0 := by
  sorry


/-! **Conclusion.** What do you think of this two-liner:
```
symm
exact zero_ne_one
```

`exact` doesn't just take hypotheses, it will eat any proof which exists
in the system. -/

/-! ## Level 11 · 2 + 2 ≠ 5

2 + 2 ≠ 5 is boring to prove in full, given only the tools we have currently.
To make it a bit less painful, I have unfolded all of the numerals for you.
See if you can use `zero_ne_succ` and `succ_inj` to prove this.
-/

/- $2+2≠5$. -/
example: succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  sorry


/-! **Conclusion.** Here's my proof:
```
intro h
rw [add_succ, add_succ, add_zero] at h
repeat apply succ_inj at h
apply zero_ne_succ at h
exact h
```

Even though Lean is a theorem prover, right now it's pretty clear that we have not
developed enough material to make it an adequate calculator. In Algorithm
World, a more computer-sciency world, we will develop machinery which makes
questions like this much easier, and goals like $20 + 20 ≠ 41$ feasible.
Alternatively you can do more mathematics in Advanced Addition World, where we prove
the lemmas needed to get a working theory of inequalities. Click "Home" and
decide your route. -/

end MyNat
