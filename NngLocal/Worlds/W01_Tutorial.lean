import NngLocal.MyNat.Addition
import NngLocal.MyNat.Definition
import NngLocal.MyNat.Multiplication
import NngLocal.MyNat.TutorialLemmas
import NngLocal.Tactic.Cases
import NngLocal.Tactic.FromMathlib
import NngLocal.Tactic.Induction
import NngLocal.Tactic.Ne
import NngLocal.Tactic.Rfl
import NngLocal.Tactic.Rw
import NngLocal.Tactic.SimpAdd
import NngLocal.Tactic.Use

/-! # Tutorial World

Welcome to tutorial world! In this world we learn the basics
of proving theorems. The boss level of this world
is the theorem `2 + 2 = 4`.

You prove theorems by solving puzzles using tools called *tactics*.
The aim is to prove the theorem by applying tactics
in the right order.

Let's learn some basic tactics. Click on "Start" below
to begin your quest.

Extracted from NNG4 `Game/Levels/Tutorial`. Replace each `sorry` with a proof.
-/

namespace MyNat

/-! ## Level 1 · The rfl tactic

# Read this first

Each level in this game involves proving a mathematical theorem (the "Goal").
The goal will be a statement about *numbers*. Some numbers in this game have known values.
Those numbers have names like $37$. Other numbers will be secret. They're called things
like $x$ and $q$. We know $x$ is a number, we just don't know which one.

In this first level we're going to prove the theorem that $37x + q = 37x + q$.
You can see `x q : ℕ` in the *Objects* below, which means that `x` and `q`
are numbers.

We solve goals in Lean using *Tactics*, and the first tactic we're
going to learn is called `rfl`, which proves all theorems of the form $X = X$.

Prove that $37x+q=37x+q$ by executing the `rfl` tactic.

### Tactic `rfl`

## Summary

`rfl` proves goals of the form `X = X`.

In other words, the `rfl` tactic will close any goal of the
form `A = B` if `A` and `B` are *identical*.

`rfl` is short for \"reflexivity (of equality)\".

## Example:

If the goal looks like this:

```
x + 37 = x + 37
```

then `rfl` will close it. But if it looks like `0 + x = x` then `rfl` won't work, because even
though $0+x$ and $x$ are always equal as *numbers*, they are not equal as *terms*.
The only term which is identical to `0 + x` is `0 + x`.

## Details

`rfl` is short for \"reflexivity of equality\".

## Game Implementation

*Note that our `rfl` is weaker than the version used in core Lean and `mathlib`,
for pedagogical purposes; mathematicians do not distinguish between propositional
and definitional equality because they think about definitions in a different way
to type theorists (`zero_add` and `add_zero` are both \"facts\" as far
as mathematicians are concerned, and who cares what the definition of addition is).*
-/

/- If $x$ and $q$ are arbitrary natural numbers, then $37x+q=37x+q.$ -/
example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  -- Hint: In order to use the tactic `rfl` you can enter it in the text box
  --     under the goal and hit "Execute".
  sorry


/-! **Conclusion.** Congratulations! You completed your first verified proof!

Remember that `rfl` is a *tactic*. If you ever want information about the `rfl` tactic,
you can click on `rfl` in the list of tactics on the right.

Now click on "Next" to learn about the `rw` tactic. -/

/-! ## Level 2 · the rw tactic

In this level the *goal* is $2y=2(x+7)$ but to help us we
have an *assumption* `h` saying that $y = x + 7$. Check that you can see `h` in
your list of assumptions. Lean thinks of `h` as being a secret proof of the
assumption, rather like `x` is a secret number.

Before we can use `rfl`, we have to "substitute in for $y$".
We do this in Lean by *rewriting* the goal with `h`,
using the `rw` tactic.

### Tactic `rw`

## Summary

If `h` is a proof of an equality `X = Y`, then `rw [h]` will change
all `X`s in the goal to `Y`s. It's the way to \"substitute in\".

## Variants

* `rw [← h]` (changes `Y`s to `X`s; get the back arrow by typing `\left ` or `\l`.)

* `rw [h1, h2]` (a sequence of rewrites)

* `rw [h] at h2` (changes `X`s to `Y`s in hypothesis `h2`)

* `rw [h] at h1 h2 ⊢` (changes `X`s to `Y`s in two hypotheses and the goal;
get the `⊢` symbol with `\|-`.)

* `repeat rw [add_zero]` will keep changing `? + 0` to `?`
until there are no more matches for `? + 0`.

* `nth_rewrite 2 [h]` will change only the second `X` in the goal to `Y`.

### Example:

If you have the assumption `h : x = y + y` and your goal is
```
succ (x + 0) = succ (y + y)
```

then

`rw [add_zero]`

will change the goal into `succ x = succ (y + y)`, and then

`rw [h]`

will change the goal into `succ (y + y) = succ (y + y)`, which
can be solved with `rfl`.

### Example:

You can use `rw` to change a hypothesis as well.
For example, if you have two hypotheses
```
h1 : x = y + 3
h2 : 2 * y = x
```
then `rw [h1] at h2` will turn `h2` into `h2 : 2 * y = y + 3`.

## Common errors

* You need the square brackets. `rw h` is never correct.

* If `h` is not a *proof* of an *equality* (a statement of the form `A = B`),
for example if `h` is a function or an implication,
then `rw` is not the tactic you want to use. For example,
`rw [P = Q]` is never correct: `P = Q` is the theorem *statement*,
not the proof. If `h : P = Q` is the proof, then `rw [h]` will work.

## Details

The `rw` tactic is a way to do \"substituting in\". There
are two distinct situations where you can use this tactic.

1) Basic usage: if `h : A = B` is an assumption or
the proof of a theorem, and if the goal contains one or more `A`s, then `rw [h]`
will change them all to `B`s. The tactic will error
if there are no `A`s in the goal.

2) Advanced usage: Assumptions coming from theorem proofs
often have missing pieces. For example `add_zero`
is a proof that `? + 0 = ?` because `add_zero` really is a function,
and `?` is the input. In this situation `rw` will look through the goal
for any subterm of the form `x + 0`, and the moment it
finds one it fixes `?` to be `x` then changes all `x + 0`s to `x`s.

Exercise: think about why `rw [add_zero]` changes the term
`(0 + 0) + (x + 0) + (0 + 0) + (x + 0)` to
`0 + (x + 0) + 0 + (x + 0)`

If you can't remember the name of the proof of an equality, look it up in
the list of lemmas on the right.

## Targeted usage

If your goal is `b + c + a = b + (a + c)` and you want to rewrite `a + c`
to `c + a`, then `rw [add_comm]` will not work because Lean finds another
addition first and swaps those inputs instead. Use `rw [add_comm a c]` to
guarantee that Lean rewrites `a + c` to `c + a`. This works because
`add_comm` is a proof that `?1 + ?2 = ?2 + ?1`, `add_comm a` is a proof
that `a + ? = ? + a`, and `add_comm a c` is a proof that `a + c = c + a`.

If `h : X = Y` then `rw [h]` will turn all `X`s into `Y`s.
If you only want to change the 37th occurrence of `X`
to `Y` then do `nth_rewrite 37 [h]`.
-/

/- If $x$ and $y$ are natural numbers, and $y = x + 7$, then $2y = 2(x + 7)$. -/
example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  -- Hint: First execute `rw [h]` to replace the `y` with `x + 7`.
  -- Hint: Can you take it from here? Click on "Show more help!" if you need a hint.
  -- Hint (hidden): Now `rfl` will work.
  sorry


/-! **Conclusion.** You now know enough tactics to prove `2 + 2 = 4`! Let's begin the journey. -/

/-! ## Level 3 · Numbers

## The birth of number.

Numbers in Lean are defined by two rules.

* `0` is a number.
* If `n` is a number, then the *successor* `succ n` of `n` is a number.

The successor of `n` means the number after `n`. Let's learn to
count, and name a few small numbers.

## Counting to four.

`0` is a number, so `succ 0` is a number. Let's call this new number `1`.
Similarly let's define `2 = succ 1`, `3 = succ 2` and `4 = succ 3`.
This gives us plenty of numbers to be getting along with.

The *proof* that `2 = succ 1` is called `two_eq_succ_one`.
Check out the "012" tab in the list of lemmas on the right
for this and other proofs.

Let's prove that $2$ is the number after the number after zero.

### New theorems

* `one_eq_succ_zero` — `one_eq_succ_zero` is a proof of `1 = succ 0`.
* `two_eq_succ_one` — `two_eq_succ_one` is a proof of `2 = succ 1`.
* `three_eq_succ_two` — `three_eq_succ_two` is a proof of `3 = succ 2`.
* `four_eq_succ_three` — `four_eq_succ_three` is a proof of `4 = succ 3`.
-/

/- $2$ is the number after the number after $0$. -/
example: 2 = succ (succ 0) := by
  -- Hint: Start with `rw [two_eq_succ_one]` to begin to break `2` down into its definition.
  -- Hint: Can you take it from here?
  -- Hint (hidden): Next turn `1` into `succ 0` with `rw [one_eq_succ_zero]`.
  -- Hint (hidden): Now finish the job with `rfl`.
  sorry


/-! **Conclusion.** Note that you can do `rw [two_eq_succ_one, one_eq_succ_zero]`
and then `rfl` to solve this level in two lines. -/

/-! ## Level 4 · rewriting backwards

If `h` is a proof of `X = Y` then `rw [h]` will
turn `X`s into `Y`s. But what if we want to
turn `Y`s into `X`s? To tell the `rw` tactic
we want this, we use a left arrow `←`. Type
`\l` and then hit the space bar to get this arrow.

Let's prove that $2$ is the number after the number
after $0$ again, this time by changing `succ (succ 0)`
into `2`.
-/

/- $2$ is the number after the number after $0$. -/
example: 2 = succ (succ 0) := by
  -- Hint: Try `rw [← one_eq_succ_zero]` to change `succ 0` into `1`.
  -- Hint: Can you now change the goal into `2 = 2`?
  -- Hint (hidden): Now `rw [← two_eq_succ_one]` will change `succ 1` into `2`.
  sorry


/-! **Conclusion.** Why did we not just define `succ n` to be `n + 1`? Because we have not
even *defined* addition yet! We'll do that in the next level. -/

/-! ## Level 5 · Adding zero

We'd like to prove `2 + 2 = 4` but right now
we can't even *state* it
because we haven't yet defined addition.

## Defining addition.

How are we going to add $37$ to an arbitrary number $x$? Well,
there are only two ways to make numbers in this game: $0$
and successors. So to define `37 + x` we will need
to know what `37 + 0` is and what `37 + succ x` is.
Let's start with adding `0`.

### Adding 0

To make addition agree with our intuition, we should *define* `37 + 0`
to be `37`. More generally, we should define `a + 0` to be `a` for
any number `a`. The name of this proof in Lean is `add_zero a`.
For example `add_zero 37` is a proof of `37 + 0 = 37`,
`add_zero x` is a proof of `x + 0 = x`, and `add_zero` is a proof
of `? + 0 = ?`.

We write `add_zero x : x + 0 = x`, so `proof : statement`.

### New theorems

* `add_zero` — `add_zero a` is a proof that `a + 0 = a`. ## Summary `add_zero` is really a function, which eats a number, and returns a proof of a theorem about that number. For example `add_zero 37` is a proof that `37 + 0 = 37`. The `rw` tactic will accept `rw [add_zero]` and will try to figure out which number you omitted to input. ## Details A mathematician sometimes thinks of `add_zero` as \"one thing\", namely a proof of $\forall n ∈ ℕ, n + 0 = n$. This is just another way of saying that it's a function which can eat any number n and will return a proof that `n + 0 = n`.
-/

/- $a+(b+0)+(c+0)=a+b+c.$ -/
example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  -- Hint: `rw [add_zero]` will change `b + 0` into `b`.
  -- Hint: Now `rw [add_zero]` will change `c + 0` into `c`.
  sorry


/-! **Conclusion.** Those of you interested in speedrunning the game may want to know
that `repeat rw [add_zero]` will do both rewrites at once. -/

/-! ## Level 6 · Precision rewriting

## Precision rewriting

In the last level, there was `b + 0` and `c + 0`,
and `rw [add_zero]` changed the first one it saw,
which was `b + 0`. Let's learn how to tell Lean
to change `c + 0` first by giving `add_zero` an
explicit input.
-/

/- $a+(b+0)+(c+0)=a+b+c.$ -/
example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  -- Hint: Try `rw [add_zero c]`.
  -- Hint: `add_zero c` is a proof of `c + 0 = c` so that was what got rewritten.
  --     You can now change `b + 0` to `b` with `rw [add_zero]` or `rw [add_zero b]`. You
  --     can usually stick to `rw [add_zero]` unless you need real precision.
  sorry


/-! **Conclusion.** Let's now learn about Peano's second axiom for addition, `add_succ`. -/

/-! ## Level 7 · add_succ

Every number in Lean is either $0$ or a successor. We know how to add $0$,
but we need to figure out how to add successors. Let's say we already know
that `37 + d = q`. What should the answer to `37 + succ d` be? Well,
`succ d` is one bigger than `d`, so `37 + succ d` should be `succ q`,
the number one bigger than `q`. More generally `x + succ d` should
be `succ (x + d)`. Let's add this as a lemma.

* `add_succ x d : x + succ d = succ (x + d)`

If you ever see `... + succ ...` in your goal, `rw [add_succ]` is
normally a good idea.

Let's now prove that `succ n = n + 1`. Figure out how to get `+ succ` into
the picture, and then `rw [add_succ]`. Switch between the `+` (addition) and
`012` (numerals) tabs under "Theorems" on the right to
see which proofs you can rewrite.

### New theorems

* `add_succ` — `add_succ a b` is the proof of `a + succ b = succ (a + b)`.
-/

/-- For all natural numbers $a$, we have $\operatorname{succ}(a) = a+1$. -/
theorem succ_eq_add_one n : succ n = n + 1 := by
  -- Hint: Start by unravelling the `1`.
  -- Hint (hidden): `rw [one_eq_succ_zero]` will do this.
  -- Hint (hidden): Now you can `rw [add_succ]`
  -- Hint (hidden): And now `rw [add_zero]`
  -- Hint (hidden): And finally `rfl`.
  sorry


/-! **Conclusion.** [dramatic music]. Now are you ready to face the first boss of the game? -/

/-! ## Level 8 · 2+2=4

Good luck!

  One last hint. If `h : X = Y` then `rw [h]` will change *all* `X`s into `Y`s.
  If you only want to change one of them, say the 3rd one, then use
  `nth_rewrite 3 [h]`.
-/

/- $2+2=4$. -/
example: (2 : ℕ) + 2 = 4 := by
  -- Hint (hidden): `nth_rewrite 2 [two_eq_succ_one]` is I think quicker than `rw [two_eq_succ_one]`.
  -- Hint (hidden): Now you can `rw [add_succ]`
  sorry


/-! **Conclusion.** Here is an example proof of 2+2=4 showing off various techniques.

```lean
nth_rewrite 2 [two_eq_succ_one] -- only change the second `2` to `succ 1`.
rw [add_succ]
rw [one_eq_succ_zero]
rw [add_succ, add_zero] -- two rewrites at once
rw [← three_eq_succ_two] -- change `succ 2` to `3`
rw [← four_eq_succ_three]
rfl
```

Optional extra: you can run this proof yourself. Switch the game into "Editor mode" by clicking
on the `</>` button in the top right. You can now see your proof
written as several lines of code. Move your cursor between lines to see
the goal state at any point. Now cut and paste your code elsewhere if you
want to save it, and paste the above proof in instead. Move your cursor
around to investigate. When you've finished, click the `>_` button in the top right to
move back into "Typewriter mode".

You have finished tutorial world!
Click "Home" to go back to the
overworld, and select Addition World, where you will learn
about the `induction` tactic. -/

end MyNat
