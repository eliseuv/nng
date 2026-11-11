import NngLocal.Worlds.W02_Addition
import NngLocal.MyNat.Definition
import NngLocal.MyNat.Multiplication
import NngLocal.Tactic.Cases
import NngLocal.Tactic.FromMathlib
import NngLocal.Tactic.Induction
import NngLocal.Tactic.Ne
import NngLocal.Tactic.Rfl
import NngLocal.Tactic.Rw
import NngLocal.Tactic.SimpAdd
import NngLocal.Tactic.Use

/-! # Multiplication World

How should we define `37 * x`? Just like addition, we need to give definitions
when $x=0$ and when $x$ is a successor.

The zero case is easy: we define `37 * 0` to be `0`. Now say we know
`37 * d`. What should `37 * succ d` be? Well, that's $(d+1)$ $37$s,
so it should be `37 * d + 37`.

Here are the definitions in Lean.

  * `mul_zero a : a * 0 = 0`
  * `mul_succ a d : a * succ d = a * d + a`

In this world, we must not only prove facts about multiplication like `a * b = b * a`,
we must also prove facts about how multiplication interacts with addition, like `a * (b + c) = a * b + a * c`.
Let's get started.

Extracted from NNG4 `Game/Levels/Multiplication`. Replace each `sorry` with a proof.
-/

namespace MyNat

/-! ## Level 1 · mul_one

See the new "*" tab in your lemmas, containing `mul_zero` and `mul_succ`.
Right now these are the only facts we know about multiplication.
Let's prove nine more.

Let's start with a warm-up: no induction needed for this one,
because we know `1` is a successor.

### New theorems

* `mul_zero` — `mul_zero m` is the proof that `m * 0 = 0`.
* `mul_succ` — `mul_succ a b` is the proof that `a * succ b = a * b + a`.
-/

/-- For any natural number $m$, we have $ m \times 1 = m$. -/
theorem mul_one (m : ℕ) : m * 1 = m := by
  sorry


/-! ## Level 2 · zero_mul

Our first challenge is `mul_comm x y : x * y = y * x`,
and we want to prove it by induction. The zero
case will need `mul_zero` (which we have)
and `zero_mul` (which we don't), so let's
start with this.
-/

/-- For all natural numbers $m$, we have $ 0 \times m = 0$. -/
theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  sorry


/-! ## Level 3 · succ_mul

Similarly we have `mul_succ`
but we're going to need `succ_mul` (guess what it says -- maybe you
are getting the hang of Lean's naming conventions).

The last level from addition world might help you in this level.
If you can't remember what it is, you can go back to the
home screen by clicking the house icon and then taking a look.
You won't lose any progress.
-/

/-- For all natural numbers $a$ and $b$, we have
$(\operatorname{succ}\ a) \times b = a\times b + b$. -/
theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  sorry


/-! ## Level 4 · mul_comm

The first sub-boss of Multiplication World is `mul_comm x y : x * y = y * x`.

When you've proved this theorem we will have "spare" proofs
such as `zero_mul`, which is now easily deducible from `mul_zero`.
But we'll keep hold of these proofs anyway, because it's convenient
to have exactly the right tool for a job.
-/

/-- Multiplication is commutative. -/
theorem mul_comm (a b : ℕ) : a * b = b * a := by
  sorry


/-! ## Level 5 · one_mul

You can prove $1\times m=m$ in at least three ways.
Either by induction, or by using `succ_mul`, or
by using commutativity. Which do you think is quickest?
-/

/-- For any natural number $m$, we have $ 1 \times m = m$. -/
theorem one_mul (m : ℕ): 1 * m = m := by
  sorry


/-! **Conclusion.** Here's my solution:
```
rw [mul_comm, mul_one]
rfl
``` -/

/-! ## Level 6 · two_mul

This level is more important than you think; it plays
a useful role when battling a big boss later on.
-/

/-- For any natural number $m$, we have $ 2 \times m = m+m$. -/
theorem two_mul (m : ℕ): 2 * m = m + m := by
  sorry


/-! **Conclusion.** Here's my solution:
```
rw [two_eq_succ_one, succ_mul, one_mul]
rfl
``` -/

/-! ## Level 7 · mul_add

Our next goal is "left and right distributivity",
meaning $a(b+c)=ab+ac$ and $(b+c)a=ba+ca$. Rather than
these slightly pompous names, the name of the proofs
in Lean are descriptive. Let's start with
`mul_add a b c`, the proof of `a * (b + c) = a * b + a * c`.
Note that the left hand side contains a multiplication
and then an addition.
-/

/-- Multiplication is distributive over addition on the left.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$a(b + c) = ab + ac$. -/
theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  -- Hint: You can do induction on any of the three variables. Some choices
  --     are harder to push through than others. Can you do the inductive step in
  --     5 rewrites only?
  -- Hint (hidden): Induction on `a` is the most troublesome, then `b`,
  --     and `c` is the easiest.
  sorry


/-! **Conclusion.** Here's my solution:
```
induction c with d hd
rw [add_zero, mul_zero, add_zero]
rfl
rw [add_succ, mul_succ, hd, mul_succ, add_assoc]
rfl
```

Inducting on `a` or `b` also works, but might take longer. -/

/-! ## Level 8 · add_mul

`add_mul` is just as fiddly to prove by induction; but there's a trick
which avoids it. Can you spot it?
-/

/-- Multiplication is distributive over addition.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$(a + b) \times c = ac + bc$. -/
theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  sorry


/-! **Conclusion.** Here's my proof:
```
rw [mul_comm, mul_add]
repeat rw [mul_comm c]
rfl
``` -/

/-! ## Level 9 · mul_assoc

We now have enough to prove that multiplication is associative,
the boss level of multiplication world. Good luck!
-/

/-- Multiplication is associative.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$(ab)c = a(bc)$. -/
theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  sorry


/-! **Conclusion.** A passing mathematician notes that you've proved
that the natural numbers are a commutative semiring.

If you want to begin your journey to the final boss, head for Power World. -/

end MyNat
