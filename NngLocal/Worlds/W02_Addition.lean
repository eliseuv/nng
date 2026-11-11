import NngLocal.Worlds.W01_Tutorial
import NngLocal.MyNat.Addition
import NngLocal.MyNat.Definition
import NngLocal.Tactic.Cases
import NngLocal.Tactic.FromMathlib
import NngLocal.Tactic.Induction
import NngLocal.Tactic.Ne
import NngLocal.Tactic.Rfl
import NngLocal.Tactic.Rw
import NngLocal.Tactic.SimpAdd
import NngLocal.Tactic.Use

/-! # Addition World

Welcome to Addition World! In this world we'll learn the `induction` tactic.
This will enable us to defeat the boss level of this world, namely `x + y = y + x`.

The tactics `rw`, `rfl` and `induction` are the only tactics you'll need to
beat all the levels in Addition World, Multiplication World, and Power World.
Power World contains the final boss of the game.

There are plenty more tactics in this game, but you'll only need to know them if you
want to explore the game further (for example if you decide to 100%
the game).

Extracted from NNG4 `Game/Levels/Addition`. Replace each `sorry` with a proof.
-/

namespace MyNat

/-! ## Level 1 · zero_add

In this level we're going to prove that $0+n=n$, where $n$ is a secret natural number.

Wait, don't we already know that? No! We know that $n+0=n$, but that's `add_zero`.
This is `zero_add`, which is different.

The difficulty with proving `0 + n = n` is that we do not have a *formula* for
`0 + n` in general, we can only use `add_zero` and `add_succ` once
we know whether `n` is `0` or a successor. The `induction` tactic splits into these two cases.

The base case will require us to prove `0 + 0 = 0`, and the inductive step
will ask us to show that if `0 + d = d` then `0 + succ d = succ d`. Because
`0` and successor are the only way to make numbers, this will cover all the cases.

See if you can do your first induction proof in Lean.

(By the way, if you are still in the "Editor mode" from the last world, you can swap
back to "Typewriter mode" by clicking the `>_` button in the top right.)

### Tactic `induction`

## Summary

If `n : ℕ` is an object, and the goal mentions `n`, then `induction n with d hd`
attempts to prove the goal by induction on `n`, with the inductive
variable in the successor case being `d`, and the inductive hypothesis being `hd`.

### Example:
If the goal is
```
0 + n = n
```

then

`induction n with d hd`

will turn it into two goals. The first is `0 + 0 = 0`;
the second has an assumption `hd : 0 + d = d` and goal
`0 + succ d = succ d`.

Note that you must prove the first
goal before you can access the second one.
-/

/-- For all natural numbers $n$, we have $0 + n = n$. -/
theorem zero_add (n : ℕ) : 0 + n = n := by
  -- Hint: You can start a proof by induction on `n` by typing:
  --     `induction n with d hd`.
  -- Hint: Now you have two goals. Once you proved the first, you will jump to the second one.
  --       This first goal is the base case $n = 0$.
  --
  --       Recall that you can rewrite the proof of any lemma which is visible
  --       in your inventory, or of any assumption displayed above the goal,
  --       as long as it is of the form `X = Y`.
  -- Hint (hidden): try rewriting `add_zero`.
  -- Hint: Now for the second goal. Here you have the induction hypothesis
  --       `{hd} : 0 + {d} = {d}`, and you need to prove that `0 + succ {d} = succ {d}`.
  -- Hint (hidden): Use `add_succ`.
  -- Hint (hidden): At this point you see the term `0 + {d}`, so you can use the
  --       induction hypothesis with `rw [{hd}]`.
  sorry

attribute [simp] zero_add


/-! **Conclusion.** This lemma would have been easy if we had known that `x + y = y + x`. That theorem
  is called `add_comm` and it is *true*, but unfortunately its proof *uses* both
  `add_zero` and `zero_add`!

  Let's continue on our journey to `add_comm`, the proof of `x + y = y + x`. -/

/-! ## Level 2 · succ_add

Oh no! On the way to `add_comm`, a wild `succ_add` appears. `succ_add a b`
is the proof that `(succ a) + b = succ (a + b)` for `a` and `b` numbers.
This result is what's standing in the way of `x + y = y + x`. Again
we have the problem that we are adding `b` to things, so we need
to use induction to split into the cases where `b = 0` and `b` is a successor.
-/

/-- For all natural numbers $a, b$, we have
$ \operatorname{succ}(a) + b = \operatorname{succ}(a + b)$. -/
theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  -- Hint (hidden): You might want to think about whether induction
  --     on `a` or `b` is the best idea.
  -- Hint: Induction on `a` will not work here. You are still stuck with an `+ b`.
  --       I suggest you delete this line and try a different approach.
  -- Hint: Note that `succ a + {d}` means `(succ a) + {d}`. Put your cursor
  --     on any `succ` in the goal or assumptions to see what exactly it's eating.
  sorry


/-! **Conclusion.** Well done! You now have enough tools to tackle the main boss of this world. -/

/-! ## Level 3 · add_comm (level boss)

[boss battle music]

Look in your inventory to see the proofs you have available.
These should be enough.
-/

/-- On the set of natural numbers, addition is commutative.
In other words, if `a` and `b` are arbitrary natural numbers, then
$a + b = b + a$. -/
theorem add_comm (a b : ℕ) : a + b = b + a := by
  -- Hint (hidden): Induction on `a` or `b` -- it's all the same in this one.
  sorry

instance : Std.Commutative (α := ℕ) (· + ·) := ⟨add_comm⟩


/-! ## Level 4 · add_assoc (associativity of addition)

We've been adding up two numbers; in this level we will add up three.

  What does $x+y+z$ *mean*? It could either mean $(x+y)+z$, or it
  could mean $x+(y+z)$. In Lean, $x+y+z$ means $(x+y)+z$.

  But why do we care which one it means; $(x+y)+z$ and $x+(y+z)$ are *equal*!

  That's true, but we didn't prove it yet. Let's prove it now by induction.
-/

/-- On the set of natural numbers, addition is associative.
In other words, if $a, b$ and $c$ are arbitrary natural numbers, we have
$ (a + b) + c = a + (b + c). $ -/
theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- Hint: Remember that when Lean writes `a + b + c`, it means `(a + b) + c`.
  --     If you are not sure where the brackets are in an expression, just hover
  --     your cursor over it and look at what gets highlighted. For example,
  --     hover over both `+` symbols on the left hand side of the goal and
  --     you'll see where the invisible brackets are.
  sorry

instance : Std.Associative (α := ℕ) (· + ·) := ⟨add_assoc⟩


/-! **Conclusion.** A passing mathematician congratulates you on proving that naturals
are an additive commutative monoid.

Let's practice using `add_assoc` and `add_comm` in one more level,
before we leave addition world. -/

/-! ## Level 5 · add_right_comm

`add_comm b c` is a proof that `b + c = c + b`. But if your goal
is `a + b + c = a + c + b` then `rw [add_comm b c]` will not
work! Because the goal means `(a + b) + c = (a + c) + b` so there
is no `b + c` term *directly* in the goal.

Use associativity and commutativity to prove `add_right_comm`.
You don't need induction. `add_assoc` moves brackets around,
and `add_comm` moves variables around.

Remember that you can do more targeted rewrites by
adding explicit variables as inputs to theorems. For example `rw [add_comm b]`
will only do rewrites of the form `b + ? = ? + b`, and `rw [add_comm b c]`
will only do rewrites of the form `b + c = c + b`.
-/

/-- If $a, b$ and $c$ are arbitrary natural numbers, we have
$(a + b) + c = (a + c) + b$. -/
theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  sorry


/-! **Conclusion.** You've now seen all the tactics you need to beat the final boss of the game.
You can begin the journey towards this boss by entering Multiplication World.

Or you can go off the beaten track and learn some new tactics in Implication
World. These tactics let you prove more facts about addition, such as
how to deduce `a = 0` from `x + a = x`.

Click "Home" and make your choice. -/

end MyNat
