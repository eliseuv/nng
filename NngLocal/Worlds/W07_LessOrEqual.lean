import NngLocal.Worlds.W06_AdvAddition
import NngLocal.MyNat.Definition
import NngLocal.MyNat.LE
import NngLocal.Tactic.Cases
import NngLocal.Tactic.FromMathlib
import NngLocal.Tactic.Induction
import NngLocal.Tactic.Ne
import NngLocal.Tactic.Rfl
import NngLocal.Tactic.Rw
import NngLocal.Tactic.SimpAdd
import NngLocal.Tactic.Use

/-! # ≤ World

In this world we define `a ≤ b` and prove standard facts
about it, such as "if `a ≤ b` and `b ≤ c` then `a ≤ c`."

The definition of `a ≤ b` is "there exists a number `c`
such that `b = a + c`. " So we're going to have to learn
a tactic to prove "exists" theorems, and another one
to use "exists" hypotheses.

Click on "Start" to proceed.

Extracted from NNG4 `Game/Levels/LessOrEqual`. Replace each `sorry` with a proof.
-/

namespace MyNat

/-! ## Level 1 · The `use` tactic

`a ≤ b` is *notation* for `∃ c, b = a + c`. This "backwards E"
means "there exists". So `a ≤ b` means that there exists
a number `c` such that `b = a + c`. This definition works
because there are no negative numbers in this game.

To *prove* an "exists" statement, use the `use` tactic.
Let's see an example.

### Tactic `use`

## Summary

The `use` tactic makes progress with goals which claim something *exists*.
If the goal claims that some `x` exists with some property, and you know
that `x = 37` will work, then `use 37` will make progress.

Because `a ≤ b` is notation for \"there exists `c` such that `b = a + c`\",
you can make progress on goals of the form `a ≤ b` by `use`ing the
number which is morally `b - a` (i.e. `use b - a`)

Any of the following examples is possible assuming the type of the argument passed to the `use` function is accurate:

- `use 37`
- `use a`
- `use a * a + 1`
-/

/-- If $x$ is a number, then $x \le x$. -/
theorem le_refl (x : ℕ) : x ≤ x := by
  -- Hint: The reason `{x} ≤ {x}` is because `{x} = {x} + 0`.
  --     So you should start this proof with `use 0`.
  -- Hint: You can probably take it from here.
  sorry


/-! ## Level 2 · 0 ≤ x

To solve this level, you need to `use` a number `c` such that `x = 0 + c`.
-/

/-- If $x$ is a number, then $0 \le x$. -/
theorem zero_le (x : ℕ) : 0 ≤ x := by
  sorry


/-! ## Level 3 · x ≤ succ x

If you `use` the wrong number, you get stuck with a goal you can't prove.
What number will you `use` here?
-/

/-- If $x$ is a number, then $x \le \operatorname{succ}(x)$. -/
theorem le_succ_self (x : ℕ) : x ≤ succ x := by
  sorry


/-! **Conclusion.** Here's a two-liner:
```
use 1
exact succ_eq_add_one x
```

This works because `succ_eq_add_one x` is a proof of `succ x = x + 1`. -/

/-! ## Level 4 · x ≤ y and y ≤ z implies x ≤ z

In this level, we see inequalities as *hypotheses*. We have not seen this before.
The `cases` tactic can be used to take `hxy` apart.
-/

/-- If $x \leq y$ and $y \leq z$, then $x \leq z$. -/
theorem le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- Hint: Start with `cases {hxy} with a ha`.
  -- Hint: Now `{ha}` is a proof that `{y} = {x} + {a}`, and `hxy` has vanished. Similarly, you can destruct
  --     `{hyz}` into its parts with `cases {hyz} with b hb`.
  -- Hint: Now you need to figure out which number to `use`. See if you can take it from here.
  sorry


/-! **Conclusion.** A passing mathematician remarks that with reflexivity and transitivity out of the way,
you have proved that `≤` is a *preorder* on `ℕ`. -/

/-! ## Level 5 · x ≤ 0 → x = 0

It's "intuitively obvious" that there are no numbers less than zero,
but to prove it you will need a result which you showed in advanced
addition world.
-/

/-- If $x \leq 0$, then $x=0$. -/
theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  -- Hint (hidden): You want to use `add_right_eq_zero`, which you already
  --     proved, but you'll have to start with `symm at` your hypothesis.
  sorry


/-! ## Level 6 · x ≤ y and y ≤ x implies x = y

This level asks you to prove *antisymmetry* of $\leq$.
In other words, if $x \leq y$ and $y \leq x$ then $x = y$.
It's the trickiest one so far. Good luck!
-/

/-- If $x \leq y$ and $y \leq x$, then $x = y$. -/
theorem le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  sorry


/-! **Conclusion.** Here's my proof:
```
cases hxy with a ha
cases hyx with b hb
rw [ha]
rw [ha, add_assoc] at hb
symm at hb
apply add_right_eq_self at hb
apply add_right_eq_zero at hb
rw [hb, add_zero]
rfl
```

A passing mathematician remarks that with antisymmetry as well,
you have proved that `≤` is a *partial order* on `ℕ`.

The boss level of this world is to prove
that `≤` is a total order. Let's learn two more easy tactics
first. -/

/-! ## Level 7 · Dealing with `or`

Totality of `≤` is the boss level of this world, and it's coming up next. It says that
if `a` and `b` are naturals then either `a ≤ b` or `b ≤ a`.
But we haven't talked about `or` at all. Here's a run-through.

1) The notation for "or" is `∨`. You won't need to type it, but you can
type it with `\or`.

2) If you have an "or" statement in the *goal*, then two tactics make
progress: `left` and `right`. But don't choose a direction unless your
hypotheses guarantee that it's the correct one.

3) If you have an "or" statement as a *hypothesis* `h`, then
`cases h with h1 h2` will create two goals, one where you went left,
and the other where you went right.

### Tactic `left`

# Summary
The `left` tactic changes a goal of `P ∨ Q` into a goal of `P`.
Use it when your hypotheses guarantee that the reason that `P ∨ Q`
is true is because in fact `P` is true.

Internally this tactic is just `apply`ing a theorem
saying that $P \implies P \lor Q.$

Note that this tactic can turn a solvable goal into an unsolvable
one.

### Tactic `right`

# Summary
The `right` tactic changes a goal of `P ∨ Q` into a goal of `Q`.
Use it when your hypotheses guarantee that the reason that `P ∨ Q`
is true is because in fact `Q` is true.

Internally this tactic is just `apply`ing a theorem
saying that $Q \implies P \lor Q.$

Note that this tactic can turn a solvable goal into an unsolvable
one.
-/

/- If $x=37$ or $y=42$, then $y=42$ or $x=37$. -/
example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  -- Hint: We don't know whether to go left or right yet. So start with `cases {h} with hx hy`.
  -- Hint: Now we can prove the `or` statement by proving the statement on the right,
  --     so use the `right` tactic.
  -- Hint (hidden): This time, use the `left` tactic.
  sorry


/-! **Conclusion.** Ready for the boss level of this world? -/

/-! ## Level 8 · x ≤ y or y ≤ x

This is I think the toughest level yet. Tips: if `a` is a number
then `cases a with b` will split into cases `a = 0` and `a = succ b`.
And don't go left or right until your hypotheses guarantee that
you can prove the resulting goal!

I've left hidden hints; if you need them, retry from the beginning
and click on "Show more help!"
-/

/-- If $x$ and $y$ are numbers, then either $x \leq y$ or $y \leq x$. -/
theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  -- Hint (hidden): Start with `induction {y} with d hd`.
  -- Hint (hidden): Try `cases {hd} with h1 h2`.
  -- Hint (hidden): Now `cases {h2} with e he`.
  -- Hint (hidden): You still don't know which way to go, so do `cases {e} with a`.
  sorry


/-! **Conclusion.** Very well done.

A passing mathematician remarks that with you've just proved that `ℕ` is totally
ordered.

The final few levels in this world are much easier. -/

/-! ## Level 9 · succ x ≤ succ y → x ≤ y

We've proved that `x ≤ 0` implies `x = 0`. The last two levels
in this world will prove which numbers are `≤ 1` and `≤ 2`.
This lemma will be helpful for them.
-/

/-- If $\operatorname{succ}(x) \leq \operatorname{succ}(y)$ then $x \leq y$. -/
theorem succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  sorry


/-! **Conclusion.** Here's my proof:
```
cases hx with d hd
use d
rw [succ_add] at hd
apply succ_inj at hd
exact hd
``` -/

/-! ## Level 10 · x ≤ 1

We've seen `le_zero`, the proof that if `x ≤ 0` then `x = 0`.
Now we'll prove that if `x ≤ 1` then `x = 0` or `x = 1`.
-/

/-- If $x \leq 1$ then either $x = 0$ or $x = 1$. -/
theorem le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  sorry


/-! **Conclusion.** Here's my proof:
```
cases x with y
left
rfl
rw [one_eq_succ_zero] at hx ⊢
apply succ_le_succ at hx
apply le_zero at hx
rw [hx]
right
rfl
```

If you solved this level then you should be fine with the next level! -/

/-! ## Level 11 · le_two

We'll need this lemma to prove that two is prime!

You'll need to know that `∨` is right associative. This means that
`x = 0 ∨ x = 1 ∨ x = 2` actually means `x = 0 ∨ (x = 1 ∨ x = 2)`.
This affects how `left` and `right` work.
-/

/-- If $x \leq 2$ then $x = 0$ or $1$ or $2$. -/
theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  sorry


/-! **Conclusion.** Nice!

The next step in the development of order theory is to develop
the theory of the interplay between `≤` and multiplication.
If you've already done Multiplication World, you're now ready for
Advanced Multiplication World. Click on "Home" to access it. -/

end MyNat
