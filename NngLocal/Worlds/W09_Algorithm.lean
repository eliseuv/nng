import NngLocal.Worlds.W08_AdvMultiplication
import NngLocal.MyNat.Definition
import NngLocal.MyNat.PeanoAxioms
import NngLocal.Tactic.Cases
import NngLocal.Tactic.Decide
import NngLocal.Tactic.FromMathlib
import NngLocal.Tactic.Induction
import NngLocal.Tactic.Ne
import NngLocal.Tactic.Rfl
import NngLocal.Tactic.Rw
import NngLocal.Tactic.SimpAdd
import NngLocal.Tactic.Use

/-! # Algorithm World

Proofs like $2+2=4$ and $a+b+c+d+e=e+d+c+b+a$ are very tedious to do by hand.
In Algorithm World we learn how to get the computer to do them for us.

Click on "Start" to proceed.

Extracted from NNG4 `Game/Levels/Algorithm`. Replace each `sorry` with a proof.
-/

namespace MyNat

/-! ## Level 1 · add_left_comm

Having to rearrange variables manually using commutativity and
associativity is very tedious. We start by reminding you of this. `add_left_comm`
is a key component in the first algorithm which we'll explain, but we need
to prove it manually.

Remember that you can do precision commutativity rewriting
with things like `rw [add_comm b c]`. And remember that
`a + b + c` means `(a + b) + c`.
-/

/-- If $a, b, c$ are numbers, then $a+(b+c)=b+(a+c)$. -/
theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  sorry


/-! ## Level 2 · making life easier

In some later worlds, we're going to see some much nastier levels,
like `(a + a + 1) + (b + b + 1) = (a + b + 1) + (a + b + 1)`.
Brackets need to be moved around, and variables need to be swapped.

In this level, `(a + b) + (c + d) = ((a + c) + d) + b`,
let's forget about the brackets and just think about
the variable order.
To turn `a+b+c+d` into `a+c+d+b` we need to swap `b` and `c`,
and then swap `b` and `d`. But this is easier than you
think with `add_left_comm`.
-/

/- If $a, b$, $c$ and $d$ are numbers, we have
$(a + b) + (c + d) = ((a + c) + d) + b.$ -/
example (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  -- Hint: Start with `repeat rw [add_assoc]` to push all the brackets to the right.
  -- Hint: Now use `rw [add_left_comm b c]` to switch `b` and `c` on the left
  --     hand side.
  -- Hint: Finally use a targeted `add_comm` to switch `b` and `d`.
  -- Hint (hidden): `rw [add_comm b d]`.
  sorry


/-! **Conclusion.** So that's the algorithm: now let's use automation to perform it
automatically. -/

/-! ## Level 3 · making life simple

Lean's simplifier, `simp`, is "`rw` on steroids". It will rewrite every lemma
tagged with `simp` and every lemma fed to it by the user, as much as it can.

This level is not a level which you want to solve by hand.
Get the simplifier to solve it for you.

### Tactic `simp`

# Overview

Lean's simplifier, `simp`, will rewrite every lemma
tagged with `simp` and every lemma fed to it by the user, as much as it can.
Furthermore, it will attempt to order variables into an internal order if fed
lemmas such as `add_comm`, so that it does not go into an infinite loop.
-/

/- If $a, b,\ldots h$ are arbitrary natural numbers, we have
$(d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h$. -/
example (a b c d e f g h : ℕ) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  -- Hint: Solve this level in one line with `simp only [add_left_comm, add_comm]`
  sorry


/-! **Conclusion.** Let's now make our own tactic to do this. -/

/-! ## Level 4 · the simplest approach

You can make your own tactics in Lean.
This code here
```
macro "simp_add" : tactic => `(tactic|(
  simp only [add_assoc, add_left_comm, add_comm]))
```
was used to create a new tactic `simp_add`, which runs
`simp only [add_assoc, add_left_comm, add_comm]`.
Try running `simp_add` to solve this level!

### Tactic `simp_add`

# Overview

Our home-made tactic `simp_add` will solve arbitrary goals of
the form `a + (b + c) + (d + e) = e + (d + (c + b)) + a`.
-/

macro "simp_add" : tactic => `(tactic|(
  simp only [add_assoc, add_left_comm, add_comm]))

/- If $a, b,\ldots h$ are arbitrary natural numbers, we have
$(d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h$. -/
example (a b c d e f g h : ℕ) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  sorry


/-! **Conclusion.** Let's now move on to a more efficient approach to questions
involving numerals, such as `20 + 20 = 40`. -/

/-! ## Level 5 · pred

We now start work on an algorithm to do addition more efficiently. Recall that
we defined addition by recursion, saying what it did on `0` and successors.
It is an axiom of Lean that recursion is a valid
way to define functions from types such as the naturals.

Let's define a new function `pred` from the naturals to the naturals, which
attempts to subtract 1 from the input. The definition is this:

```
pred 0 := 37
pred (succ n) := n
```

We cannot subtract one from 0, so we just return a junk value. As well as this
definition, we also create a new lemma `pred_succ`, which says that `pred (succ n) = n`.
Let's use this lemma to prove `succ_inj`, the theorem which
Peano assumed as an axiom and which we have already used extensively without justification.

### New theorems

* `pred_succ` — `pred_succ n` is a proof of `pred (succ n) = n`.

**Not allowed in this level:** `succ_inj`
-/

/- If $\operatorname{succ}(a)=\operatorname{succ}(b)$ then $a=b$. -/
example (a b : ℕ) (h : succ a = succ b) : a = b := by
  -- Hint: Start with `rw [← pred_succ a]` and take it from there.
  sorry


/-! **Conclusion.** Nice! You've proved `succ_inj`!
Let's now prove Peano's other axiom, that successors can't be $0$. -/

/-! ## Level 6 · is_zero

We define a function `is_zero` thus:

```
is_zero 0 := True
is_zero (succ n) := False
```

We also create two lemmas, `is_zero_zero` and `is_zero_succ n`, saying that `is_zero 0 = True`
and `is_zero (succ n) = False`. Let's use these lemmas to prove `succ_ne_zero`, Peano's
Last Axiom. Actually, we have been using `zero_ne_succ` before, but it's handy to have
this opposite version too, which can be proved in the same way. Note: you can
cheat here by using `zero_ne_succ` but the point of this world is to show
you how to *prove* results like that.

If you can turn your goal into `True`, then the `trivial` tactic will solve it.

### Tactic `trivial`

# Summary

`trivial` will solve the goal `True`.

### New theorems

* `is_zero_zero` — `is_zero_zero` is a proof of `is_zero 0 = True`.
* `is_zero_succ` — `is_zero_succ a` is a proof of `is_zero (succ a) = False`.
-/

/-- $\operatorname{succ}(a) \neq 0$. -/
theorem succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
  -- Hint: Start with `intro h` (remembering that `X ≠ Y` is just notation
  --     for `X = Y → False`).
  -- Hint: We're going to change that `False` into `True`. Start by changing it into
  --     `is_zero (succ a)` by executing `rw [← is_zero_succ a]`.
  -- Hint: See if you can take it from here. Look at the new lemmas and tactic
  --     available on the right.
  sorry


/-! ## Level 7 · An algorithm for equality

Here we begin to
develop an algorithm which, given two naturals `a` and `b`, returns the answer
to "does `a = b`?"

Here is the algorithm. First note that `a` and `b` are numbers, and hence
are either `0` or successors.

*) If `a` and `b` are both `0`, return "yes".

*) If one is `0` and the other is `succ n`, return "no".

*) If `a = succ m` and `b = succ n`, then return the answer to "does `m = n`?"

Our job now is to *prove* that this algorithm always gives the correct answer. The proof that
`0 = 0` is `rfl`. The proof that `0 ≠ succ n` is `zero_ne_succ n`, and the proof
that `succ m ≠ 0` is `succ_ne_zero m`. The proof that if `h : m = n` then
`succ m = succ n` is `rw [h]` and then `rfl`. This level is a proof of the one
remaining job we have to do: if `a ≠ b` then `succ a ≠ succ b`.

### Tactic `contrapose`

# Summary

If you have a hypothesis

`h : a ≠ b`

and goal

`c ≠ d`

then `contrapose! h` replaces the set-up with its so-called \"contrapositive\":
a hypothesis

`h : c = d`

and goal

`a = b`.
-/

/-- If $a \neq b$ then $\operatorname{succ}(a) \neq\operatorname{succ}(b)$. -/
theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  -- Hint: Start with `contrapose! h`, to change the goal into its
  --     contrapositive, namely a hypothesis of `succ m = succ n` and a goal of `m = n`.
  -- Hint: Can you take it from here? (note: if you try `contrapose! h` again, it will
  --     take you back to where you started!)
  sorry


/-! Upstream support module `Game.MyNat.DecidableEq`, inlined here because it
depends on the previous level. -/

instance instDecidableEq : DecidableEq MyNat
| 0, 0 => isTrue <| by
  show 0 = 0
  rfl
| succ m, 0 => isFalse <| by
  show succ m ≠ 0
  exact succ_ne_zero m
| 0, succ n => isFalse <| by
  show 0 ≠ succ n
  exact zero_ne_succ n
| succ m, succ n =>
  match instDecidableEq m n with
  | isTrue (h : m = n) => isTrue <| by
    show succ m = succ n
    rw [h]
    rfl
  | isFalse (h : m ≠ n) => isFalse <| by
    show succ m ≠ succ n
    exact succ_ne_succ m n h

/-! ## Level 8 · decide

Implementing the algorithm for equality of naturals, and the proof that it is correct,
looks like this:

```
instance instDecidableEq : DecidableEq ℕ
| 0, 0 => isTrue <| by
  show 0 = 0
  rfl
| succ m, 0 => isFalse <| by
  show succ m ≠ 0
  exact succ_ne_zero m
| 0, succ n => isFalse <| by
  show 0 ≠ succ n
  exact zero_ne_succ n
| succ m, succ n =>
  match instDecidableEq m n with
  | isTrue (h : m = n) => isTrue <| by
    show succ m = succ n
    rw [h]
    rfl
  | isFalse (h : m ≠ n) => isFalse <| by
    show succ m ≠ succ n
    exact succ_ne_succ m n h
```

This Lean code is a formally verified algorithm for deciding equality
between two naturals. I've typed it in already, behind the scenes.
Because the algorithm is formally verified to be correct, we can
use it in Lean proofs. You can run the algorithm with the `decide` tactic.

### Tactic `decide`

# Summary

`decide` will attempt to solve a goal if it can find an algorithm which it
can run to solve it.

## Example

A term of type `DecidableEq ℕ` is an algorithm to decide whether two naturals
are equal or different. Hence, once this term is made and made into an `instance`,
the `decide` tactic can use it to solve goals of the form `a = b` or `a ≠ b`.
-/

/- $20+20=40$. -/
example: (20 : ℕ) + 20 = 40 := by
  sorry


/-! **Conclusion.** You can read more about the `decide` tactic by clicking
on it in the top right. -/

/-! ## Level 9 · decide again

We gave a pretty unsatisfactory proof of `2 + 2 ≠ 5` earlier on; now give a nicer one.
-/

/- $2+2 \neq 5.$ -/
example: (2 : ℕ) + 2 ≠ 5 := by
  sorry


/-! **Conclusion.** Congratulations! You've finished Algorithm World. These algorithms
will be helpful for you in Even-Odd World (when someone gets around to
implementing it). -/

end MyNat
