import NngLocal.Worlds.W05_Implication
import NngLocal.MyNat.Definition
import NngLocal.Tactic.Cases
import NngLocal.Tactic.FromMathlib
import NngLocal.Tactic.Induction
import NngLocal.Tactic.Ne
import NngLocal.Tactic.Rfl
import NngLocal.Tactic.Rw
import NngLocal.Tactic.SimpAdd
import NngLocal.Tactic.Use

/-! # Advanced Addition World

In Advanced Addition World we will prove some basic
addition facts such as $x+y=x\implies y=0$. The theorems
proved in this world will be used to build
a theory of inequalities in `≤` World.

Click on "Start" to proceed.

Extracted from NNG4 `Game/Levels/AdvAddition`. Replace each `sorry` with a proof.
-/

namespace MyNat

/-! ## Level 1 · add_right_cancel

In this world I will mostly leave you on your own.

`add_right_cancel a b n` is the theorem that $a+n=b+n\implies a=b$.
-/

/-- $a+n=b+n\implies a=b$. -/
theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  -- Hint (hidden): Start with induction on `n`.
  sorry


/-! **Conclusion.** Nice! -/

/-! ## Level 2 · add_left_cancel

`add_left_cancel a b n` is the theorem that $n+a=n+b\implies a=b$.
You can prove it by induction on `n` or you can deduce it from `add_right_cancel`.
-/

/-- $n+a=n+b\implies a=b$. -/
theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  sorry


/-! **Conclusion.** How about this for a proof:
```
repeat rw [add_comm n]
exact add_right_cancel a b n
``` -/

/-! ## Level 3 · add_left_eq_self

`add_left_eq_self x y` is the theorem that $x + y = y\implies x=0.$
-/

/-- $x + y = y\implies x=0.$ -/
theorem add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
  sorry


/-! **Conclusion.** Did you use induction on `y`?
Here's a two-line proof of `add_left_eq_self` which uses `add_right_cancel`.
If you want to inspect it, you can go into "Editor mode" by clicking `</>` in the top right
and then just cut and paste the proof and move your cursor around it
to see the hypotheses and goal at any given point
(although you'll lose your own proof this way). Click `>_` to get
back to "Typewriter mode".
```
nth_rewrite 2 [← zero_add y]
exact add_right_cancel x 0 y
``` -/

/-! ## Level 4 · add_right_eq_self

`add_right_eq_self x y` is the theorem that $x + y = x\implies y=0.$
Two ways to do it spring to mind; I'll mention them when you've solved it.
-/

/-- $x+y=x\implies y=0$. -/
theorem add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  -- Hint: This state is not provable! Did you maybe use `rw [add_left_eq_self] at h`
  --       instead of `apply [add_left_eq_self] at h`? You can complare the two in the inventory.
  -- Hint: This state is not provable! Did you maybe use `rw [add_left_eq_self] at h`
  --       instead of `apply [add_left_eq_self] at h`? You can complare the two in the inventory.
  sorry


/-! **Conclusion.** Here's a proof using `add_left_eq_self`:
```
rw [add_comm]
intro h
apply add_left_eq_self at h
exact h
```

and here's an even shorter one using the same idea:
```
rw [add_comm]
exact add_left_eq_self y x
```

Alternatively you can just prove it by induction on `x`:

```
induction x with d hd
intro h
rw [zero_add] at h
exact h
intro h
rw [succ_add] at h
apply succ_inj at h
apply hd at h
exact h
``` -/

/-! ## Level 5 · add_right_eq_zero

The next result we'll need in `≤` World is that if `a + b = 0` then `a = 0` and `b = 0`.
Let's prove one of these facts in this level, and the other in the next.

## A new tactic: `cases`

The `cases` tactic will split an object or hypothesis up into the possible ways
that it could have been created.

For example, sometimes you want to deal with the two cases `b = 0` and `b = succ d` separately,
but don't need the inductive hypothesis `hd` that comes with `induction b with d hd`.
In this situation you can use `cases b with d` instead. There are two ways to make
a number: it's either zero or a successor. So you will end up with two goals, one
with `b = 0` and one with `b = succ d`.

Another example: if you have a hypothesis `h : False` then you are done, because a false statement implies
any statement. Here `cases h` will close the goal, because there are *no* ways to
make a proof of `False`! So you will end up with no goals, meaning you have proved everything.

### Tactic `cases`

## Summary

If `n` is a number, then `cases n with d` will break the goal into two goals,
one with `n = 0` and the other with `n = succ d`.

If `h` is a proof (for example a hypothesis), then `cases h with...` will break the
proof up into the pieces used to prove it.

## Example

If `n : ℕ` is a number, then `cases n with d` will break the goal into two goals,
one with `n` replaced by 0 and the other with `n` replaced by `succ d`. This
corresponds to the mathematical idea that every natural number is either `0`
or a successor.

## Example

If `h : P ∨ Q` is a hypothesis, then `cases h with hp hq` will turn one goal
into two goals, one with a hypothesis `hp : P` and the other with a
hypothesis `hq : Q`.

## Example

If `h : False` is a hypothesis, then `cases h` will turn one goal into no goals,
because there are no ways to make a proof of `False`! And if you have no goals left,
you have finished the level.

## Example

If `h : a ≤ b` is a hypothesis, then `cases h with c hc` will create a new number `c`
and a proof `hc : b = a + c`. This is because the *definition* of `a ≤ b` is
`∃ c, b = a + c`.
-/

/-- If $a+b=0$ then $a=0$. -/
theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  -- Hint: Here we want to deal with the cases `b = 0` and `b ≠ 0` separately,
  --     so start with `cases b with d`.
  sorry


/-! **Conclusion.** Well done! -/

/-! ## Level 6 · add_left_eq_zero

You can just mimic the previous proof to do this one -- or you can figure out a way
of using it.
-/

/-- If $a+b=0$ then $b=0$. -/
theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  sorry


/-! **Conclusion.** How about this for a proof:

```
rw [add_comm]
exact add_right_eq_zero b a
```

That's the end of Advanced Addition World! You'll need these theorems
for the next world, `≤` World. Click on "Home" to access it. -/

end MyNat
