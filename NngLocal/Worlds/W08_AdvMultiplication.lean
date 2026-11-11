import NngLocal.Worlds.W07_LessOrEqual
import NngLocal.MyNat.Definition
import NngLocal.Tactic.Cases
import NngLocal.Tactic.FromMathlib
import NngLocal.Tactic.Induction
import NngLocal.Tactic.Ne
import NngLocal.Tactic.Rfl
import NngLocal.Tactic.Rw
import NngLocal.Tactic.SimpAdd
import NngLocal.Tactic.Use

/-! # Advanced Multiplication World

Advanced *Addition* World proved various implications
involving addition, such as `x + y = 0 → x = 0` and `x + y = x → y = 0`.
These lemmas were used to prove basic facts about ≤ in ≤ World.

In Advanced Multiplication World we prove analogous
facts about multiplication, such as `x * y = 1 → x = 1`, and
`x * y = x → y = 1` (assuming `x ≠ 0` in the latter result). This will prepare
us for Divisibility World.

Multiplication World is more complex than Addition World. In the same
way, Advanced Multiplication world is more complex than Advanced Addition
World. One reason for this is that certain intermediate results are only
true under the additional hypothesis that one of the variables is non-zero.
This causes some unexpected extra twists.

Extracted from NNG4 `Game/Levels/AdvMultiplication`. Replace each `sorry` with a proof.
-/

namespace MyNat

/-! ## Level 1 · mul_le_mul_right

Let's warm up with an easy one, which works even if `t = 0`.
-/

theorem mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  sorry


/-! **Conclusion.** My proof:
```
cases h with d hd
use d * t
rw [hd, add_mul]
rfl
``` -/

/-! ## Level 2 · mul_left_ne_zero

If you have completed Algorithm World then you can use the `contrapose!` tactic
here. If not then I'll talk you through a manual approach.
-/

theorem mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  -- Hint: We want to reduce this to a hypothesis `b = 0` and a goal `a * b = 0`,
  --     which is logically equivalent but much easier to prove. Remember that `X ≠ 0`
  --     is notation for `X = 0 → False`. Click on "Show more help!" if you need hints.
  -- Hint (hidden): Start with `intro hb`.
  -- Hint (hidden): Now `apply h` and you can probably take it from here.
  sorry


/-! ## Level 3 · eq_succ_of_ne_zero

Multiplication usually makes a number bigger, but multiplication by zero can make
it smaller. Thus many lemmas about inequalities and multiplication need the
hypothesis `a ≠ 0`. Here is a key lemma that enables us to use this hypothesis.
To help us with the proof, we can use the `tauto` tactic. Click on the tactic's name
on the right to see what it does.

### Tactic `tauto`

# Summary

The `tauto` tactic will solve any goal which can be solved purely by logic (that is, by
truth tables).

## Details

`tauto` *does not do magic*! It doesn't know *anything* about addition or multiplication,
it doesn't even know `add_zero`. The only things that `tauto` knows about numbers
are firstly that `a = a` and secondly that `0 ≠ 1`, `0 ≠ 2`, `1 ≠ 2` and so on.
What `tauto`'s strength is, is *logic*. If you have a hypothesis `x < 37`
and another hypothesis `x < 37 → y + z = 42` and your goal is `y + z = 42` then `tauto` will
solve this goal, because to solve that goal you don't need to know any facts
about inequalities or addition, all you need to know is the rules of logic.

## Example

If you have `False` as a hypothesis, then `tauto` will solve
the goal. This is because a false hypothesis implies any hypothesis.

## Example

If your goal is `True`, then `tauto` will solve the goal.

## Example

If you have two hypotheses `h1 : a = 37` and `h2 : a ≠ 37` then `tauto` will
solve the goal because it can prove `False` from your hypotheses, and thus
prove the goal (as `False` implies anything).

## Example

If you have one hypothesis `h : a ≠ a` then `tauto` will solve the goal because
`tauto` is smart enough to know that `a = a` is true, which gives the contradiction we seek.

## Example

If you have a hypothesis `h : 0 = 1` then `tauto` will solve the goal, because
`tauto` knows `0 ≠ 1` and this is enough to prove `False`, which implies any goal.

## Example

If you have a hypothesis of the form `a = 0 → a * b = 0` and your goal is `a * b ≠ 0 → a ≠ 0`, then
`tauto` will solve the goal, because the goal is logically equivalent to the hypothesis.
If you switch the goal and hypothesis in this example, `tauto` would solve it too.
-/

theorem eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
  -- Hint: Start with `cases a with d` to do a case split on `a = 0` and `a = succ d`.
  -- Hint: In the "base case" we have a hypothesis `ha : 0 ≠ 0`, and you can deduce anything
  --     from a false statement. The `tauto` tactic will close this goal.
  sorry


/-! ## Level 4 · one_le_of_ne_zero

The previous lemma can be used to prove this one.
-/

theorem one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  -- Hint (hidden): Use the previous lemma with `apply eq_succ_of_ne_zero at ha`.
  -- Hint (hidden): Now take apart the existence statement with `cases ha with n hn`.
  sorry


/-! ## Level 5 · le_mul_right

One day this game will have a Prime Number World, with a final boss
of proving that $2$ is prime.
To do this, we will have to rule out things like $2 = 37 × 42$.
We will do this by proving that any factor of $2$ is at most $2$,
which we will do using this lemma. The proof I have in mind manipulates the hypothesis
until it becomes the goal, using `mul_left_ne_zero`, `one_le_of_ne_zero` and
`mul_le_mul_right`.
-/

theorem le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  sorry


/-! **Conclusion.** Here's what I was thinking of:
```
apply mul_left_ne_zero at h
apply one_le_of_ne_zero at h
apply mul_le_mul_right 1 b a at h
rw [one_mul, mul_comm] at h
exact h
``` -/

/-! ## Level 6 · mul_right_eq_one

This level proves `x * y = 1 → x = 1`, the multiplicative analogue of Advanced Addition
World's `x + y = 0 → x = 0`. The strategy is to prove that `x ≤ 1` and then use the
lemma `le_one` from `≤` world.

We'll prove it using a new and very useful tactic called `have`.

### Tactic `«have»`

# Summary

The `have` tactic can be used to add new hypotheses to a level, but of course
you have to prove them.


## Example

The simplest usage is like this. If you have `a` in your context and you execute

`have ha : a = 0`

then you will get a new goal `a = 0` to prove, and after you've proved
it you will have a new hypothesis `ha : a = 0` in your original goal.

## Example

If you already have a proof of what you want to `have`, you
can just create it immediately. For example, if you have `a` and `b`
number objects, then

`have h2 : succ a = succ b → a = b := succ_inj a b`

will directly add a new hypothesis `h2 : succ a = succ b → a = b`
to the context, because you just supplied the proof of it (`succ_inj a b`).

## Example

If you have a proof to hand, then you don't even need to state what you
are proving. For example

`have h2 := succ_inj a b`

will add `h2 : succ a = succ b → a = b` as a hypothesis.
-/

theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  -- Hint: We want to use `le_mul_right`, but we need a hypothesis `x * y ≠ 0`
  --     which we don't have. Yet. Execute `have h2 : x * y ≠ 0` (you can type `≠` with `\ne`).
  --     You'll be asked to
  --     prove it, and then you'll have a new hypothesis which you can apply
  --     `le_mul_right` to.
  -- Hint (hidden): Now you can `apply le_mul_right at h2`.
  -- Hint (hidden): Now `rw [{h}] at {h2}` so you can `apply le_one at {h2}`.
  -- Hint (hidden): Now `cases h2 with h0 h1` and deal with the two
  --     cases separately.
  -- Hint (hidden): `tauto` is good enough to solve this goal.
  sorry


/-! ## Level 7 · mul_ne_zero

This level proves that if `a ≠ 0` and `b ≠ 0` then `a * b ≠ 0`. One strategy
is to write both `a` and `b` as `succ` of something, deduce that `a * b` is
also `succ` of something, and then `apply zero_ne_succ`.
-/

theorem mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  -- Hint (hidden): Start with `apply eq_succ_of_ne_zero at ha` and `... at hb`
  sorry


/-! ## Level 8 · mul_eq_zero

This level proves that if `a * b = 0` then `a = 0` or `b = 0`. It is
logically equivalent to the last level, so there is a very short proof.
-/

theorem mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  -- Hint (hidden): Start with `have h2 := mul_ne_zero a b`.
  -- Hint (hidden): Now the goal can be deduced from `h2` by pure logic, so use the `tauto`
  --     tactic.
  sorry


/-! **Conclusion.** Here's the short proof:
```
have h2 := mul_ne_zero a b
tauto
```
This works because, given `mul_ne_zero a b`,
the argument is reduced to pure logic. -/

/-! ## Level 9 · mul_left_cancel

In this level we prove that if `a * b = a * c` and `a ≠ 0` then `b = c`. It is tricky, for
several reasons. One of these is that
we need to introduce a new idea: we will need to understand the concept of
mathematical induction a little better.

Starting with `induction b with d hd` is too naive, because in the inductive step
the hypothesis is `a * d = a * c → d = c` but what we know is `a * succ d = a * c`,
so the induction hypothesis does not apply!

Assume `a ≠ 0` is fixed. The actual statement we want to prove by induction on `b` is
"for all `c`, if `a * b = a * c` then `b = c`". This *can* be proved by induction,
because we now have the flexibility to change `c`.
-/

theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  -- Hint: The way to start this proof is `induction b with d hd generalizing c`.
  -- Hint (hidden): Use `mul_eq_zero` and remember that `tauto` will solve a goal
  --     if there are hypotheses `a = 0` and `a ≠ 0`.
  -- Hint: The inductive hypothesis `hd` is "For all natural numbers `c`, `a * d = a * c → d = c`".
  --       You can `apply` it `at` any hypothesis of the form `a * d = a * ?`.
  -- Hint (hidden): Split into cases `c = 0` and `c = succ e` with `cases c with e`.
  sorry


/-! ## Level 10 · mul_right_eq_self

The lemma proved in the final level of this world will be helpful
in Divisibility World.
-/

theorem mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  -- Hint (hidden): Reduce to the previous lemma with `nth_rewrite 2 [← mul_one a] at h`
  -- Hint (hidden): You can now `apply mul_left_cancel at h`
  sorry


/-! **Conclusion.** A two-line proof is

```
nth_rewrite 2 [← mul_one a] at h
exact mul_left_cancel a b 1 ha h
```

We now have all the tools necessary to set up the basic theory of divisibility of naturals. -/

end MyNat
