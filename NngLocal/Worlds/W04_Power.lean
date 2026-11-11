import NngLocal.Worlds.W03_Multiplication
import NngLocal.MyNat.Definition
import NngLocal.MyNat.Power
import NngLocal.Tactic.Cases
import NngLocal.Tactic.FromMathlib
import NngLocal.Tactic.Induction
import NngLocal.Tactic.Ne
import NngLocal.Tactic.Rfl
import NngLocal.Tactic.Rw
import NngLocal.Tactic.SimpAdd
import NngLocal.Tactic.Use

/-! # Power World

This world introduces exponentiation. If you want to define `37 ^ n`
then, as always, you will need to know what `37 ^ 0` is, and
what `37 ^ (succ d)` is, given only `37 ^ d`.

You can probably guess the names of the general theorems:

  * `pow_zero (a : ℕ) : a ^ 0 = 1`
  * `pow_succ (a b : ℕ) : a ^ succ b = a ^ b * a`

Using only these, can you get past the final boss level?

The levels in this world were designed by Sian Carey, a UROP student
at Imperial College London, funded by a Mary Lister McCammon Fellowship
in the summer of 2019. Thanks to Sian and also thanks to Imperial
College for funding her.

Extracted from NNG4 `Game/Levels/Power`. Replace each `sorry` with a proof.
-/

namespace MyNat

/-! ## Level 1 · zero_pow_zero

Mathematicians sometimes debate what `0 ^ 0` is;
the answer depends, of course, on your definitions. In this
game, `0 ^ 0 = 1`. See if you can prove it.

Check out the *Pow* tab in your list of theorems
to see the new proofs which are available.

### New theorems

* `pow_zero` — `pow_zero a : a ^ 0 = 1` is one of the two axioms defining exponentiation in this game.
-/

/-- $0 ^ 0 = 1$ -/
theorem zero_pow_zero: (0 : ℕ) ^ 0 = 1 := by
  sorry


/-! ## Level 2 · zero_pow_succ

We've just seen that `0 ^ 0 = 1`, but if `n`
is a successor, then `0 ^ n = 0`. We prove that here.

### New theorems

* `pow_succ` — `pow_succ a b : a ^ (succ b) = a ^ b * a` is one of the two axioms defining exponentiation in this game.
-/

/-- For all numbers $m$, $0 ^{\operatorname{succ} (m)} = 0$. -/
theorem zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (succ m) = 0 := by
  sorry


/-! ## Level 3 · pow_one
-/

/-- For all naturals $a$, $a ^ 1 = a$. -/
theorem pow_one (a : ℕ) : a ^ 1 = a := by
  sorry


/-! ## Level 4 · one_pow
-/

/-- For all naturals $m$, $1 ^ m = 1$. -/
theorem one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  sorry


/-! ## Level 5 · pow_two

Note: this lemma will be useful for the final boss!
-/

/-- For all naturals $a$, $a ^ 2 = a \times a$. -/
theorem pow_two (a : ℕ) : a ^ 2 = a * a := by
  sorry


/-! ## Level 6 · pow_add

Let's now begin our approach to the final boss,
by proving some more subtle facts about powers.
-/

/-- For all naturals $a$, $m$, $n$, we have $a^{m + n} = a ^ m  a ^ n$. -/
theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  sorry


/-! ## Level 7 · mul_pow

The music gets ever more dramatic, as we explore
the interplay between exponentiation and multiplication.

If you're having trouble exchanging the right `a * b`
because `rw [mul_comm]` swaps the wrong multiplication,
then read the documentation of `rw` for tips on how to fix this.
-/

/-- For all naturals $a$, $b$, $n$, we have $(ab) ^ n = a ^ nb ^ n$. -/
theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  sorry


/-! ## Level 8 · pow_pow

One of the best named levels in the game, a savage `pow_pow`
sub-boss appears as the music reaches a frenzy. What
else could there be to prove about powers after this?
-/

/-- For all naturals $a$, $m$, $n$, we have $(a ^ m) ^ n = a ^ {mn}$. -/
theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  sorry

attribute [simp] MyNat.pow_zero

attribute [simp] MyNat.pow_succ

attribute [simp] MyNat.pow_one

attribute [simp] MyNat.one_pow

attribute [simp] MyNat.pow_pow -- yes or no?


/-! **Conclusion.** The music dies down. Is that it?

Course it isn't, you can
clearly see that there are two levels left.

A passing mathematician says that mathematicians don't have a name
for the structure you just constructed. You feel cheated.

Suddenly the music starts up again. This really is the final boss. -/

/-! ## Level 9 · add_sq

[final boss music]
-/

/-- For all numbers $a$ and $b$, we have
$$(a+b)^2=a^2+b^2+2ab.$$ -/
theorem add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  sorry


/-! **Conclusion.** It's all over! You have proved a theorem which has tripped up
schoolkids for generations (some of them think $(a+b)^2=a^2+b^2$:
this is "the freshman's dream").

How many rewrites did you use? I can do it in 12.

But wait! This boss is stirring...and mutating into a second more powerful form! -/

/-! ## Level 10 · Fermat's Last Theorem

We now have enough to state a mathematically accurate, but slightly
clunky, version of Fermat's Last Theorem.

Fermat's Last Theorem states that if $x,y,z>0$ and $m \geq 3$ then $x^m+y^m\not =z^m$.
If you didn't do inequality world yet then we can't talk about $m \geq 3$,
so we have to resort to the hack of using `n + 3` for `m`,
which guarantees it's big enough. Similarly instead of `x > 0` we
use `a + 1`.

This level looks superficially like other levels we have seen,
but the shortest solution known to humans would translate into
many millions of lines of Lean code. The author of this game,
Kevin Buzzard, is working on translating the proof by Wiles
and Taylor into Lean, although this task will take many years.

## CONGRATULATIONS!

You've finished the main quest of the natural number game!
If you would like to learn more about how to use Lean to
prove theorems in mathematics, then take a look
at [Mathematics In Lean](https://leanprover-community.github.io/mathematics_in_lean/),
an interactive textbook which you can read in your browser,
and which explains how to work with many more mathematical concepts in Lean.
-/

/- For all naturals $a$ $b$ $c$ and $n$, we have
$$(a+1)^{n+3}+(b+1)^{n+3}\not=(c+1)^{n+3}.$$ -/
example (a b c n : ℕ) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by
  sorry


/-! **Conclusion.** Congratulations! You have proved Fermat's Last Theorem!

Either that, or you used magic... -/

end MyNat
