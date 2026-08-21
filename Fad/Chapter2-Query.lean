import Fad.QueryModel

/-!
# Chapter 2 complexity examples, in the *query model*

This module reimplements the running-time examples of `Fad.Chapter2`
(`append`, `concat₁`, `concat₂`) using the query model of `Fad.QueryModel`
instead of the `TimeM` monad, so the two styles can be compared directly.

The correspondence is:

| `TimeM` version (`Chapter2`)            | query-model version (here)            |
|-----------------------------------------|---------------------------------------|
| cost is *carried* by the computation    | cost is *assigned* by a `Model`       |
| `✓ e` / `✓[c] e` ticks inline           | a query node is emitted; its cost     |
|                                         | comes from the model, not the program |
| `.time` reads the accumulated cost      | `.runtime model` evaluates the tree   |
| one fixed cost model                    | the same program, many models         |

The complexity theorems (`concat₁_runtime`, `concat₂_runtime`) are the
query-model analogues of `Chapter2.concat₁''_time` and
`Chapter2.concat₂'_time`; compare the proofs.
-/

set_option autoImplicit false

namespace Chapter2Query

open QueryModel
open QueryModel.Prog (lift)

/-! ## `append`

The `TimeM` version (`Chapter2.append'`) prepends the head of `xs` one element
at a time, charging one tick per element:

```
def append' : List a → List a → TimeM Nat (List a)
  | [], ys       => pure ys
  | x :: xs, ys  => do ✓ return x :: (← append' xs ys)
```

Here each prepend is a *query* `AppendOp.step`; how much it costs is decided by
the model, not written into the algorithm. -/

inductive AppendOp (a : Type) : Type → Type where
  | step : a → List a → AppendOp a (List a)   -- prepend the head onto the tail

def append {a : Type} : List a → List a → Prog (AppendOp a) (List a)
  | [],      ys => pure ys
  | x :: xs, ys => do
      let r ← append xs ys
      lift (AppendOp.step x r)

/-- The natural model: a `step` prepends, and costs one unit — matching the
single `✓` per element in `Chapter2.append'`. -/
def stepCost {a : Type} : Model (AppendOp a) Nat where
  evalQuery | .step x xs => x :: xs
  cost      | .step _ _  => 1

/-- A *different* model for the *same* program: charge two units per prepend
(e.g. two memory writes). Impossible to express with `TimeM` without editing
the algorithm — the whole point of the query model. -/
def stepCost2 {a : Type} : Model (AppendOp a) Nat where
  evalQuery | .step x xs => x :: xs
  cost      | .step _ _  => 2

-- model equations (kept as simp lemmas so proofs never have to *unfold* the
-- model, which would break matching against the induction hypothesis)
@[simp] theorem stepCost_eval {a : Type} (x : a) (xs : List a) :
    stepCost.evalQuery (AppendOp.step x xs) = x :: xs := rfl
@[simp] theorem stepCost_cost {a : Type} (x : a) (xs : List a) :
    stepCost.cost (AppendOp.step x xs) = 1 := rfl
@[simp] theorem stepCost2_cost {a : Type} (x : a) (xs : List a) :
    stepCost2.cost (AppendOp.step x xs) = 2 := rfl

/-- The program still computes the ordinary append. -/
@[simp] theorem append_result {a : Type} (xs ys : List a) :
    (append xs ys).result stepCost = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]

/-- Cost under `stepCost` is the length of the first list — `Θ(|xs|)`. -/
theorem append_runtime {a : Type} (xs ys : List a) :
    (append xs ys).runtime stepCost = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]

/-- The same program, measured under `stepCost2`, costs twice as much — no
change to `append` itself. -/
theorem append_runtime2 {a : Type} (xs ys : List a) :
    (append xs ys).runtime stepCost2 = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [append, Prog.bind_eq, Prog.runtime_bind, Prog.runtime_lift,
        stepCost2_cost, List.length_cons, ih]
      omega


/-! ## `concat`

`Chapter2.concat₁''` folds append from the right, charging `xs.length` for each
append (`✓[xs.length]`). We model one append of a length-`k` list as a single
query whose *cost is `k`*, decided by the model. -/

inductive ConcatOp (a : Type) : Type → Type where
  | app : List a → List a → ConcatOp a (List a)   -- xs ++ ys

def concatCost {a : Type} : Model (ConcatOp a) Nat where
  evalQuery | .app xs ys => xs ++ ys
  cost      | .app xs _  => xs.length

@[simp] theorem concatCost_eval {a : Type} (xs ys : List a) :
    concatCost.evalQuery (ConcatOp.app xs ys) = xs ++ ys := rfl
@[simp] theorem concatCost_cost {a : Type} (xs ys : List a) :
    concatCost.cost (ConcatOp.app xs ys) = xs.length := rfl

/-- Right fold — mirrors `Chapter2.concat₁''`. -/
def concat₁ {a : Type} : List (List a) → Prog (ConcatOp a) (List a)
  | []        => pure []
  | xs :: xss => do
      let ys ← concat₁ xss
      lift (ConcatOp.app xs ys)

/-- Left fold, cost-charging on the accumulator — mirrors `Chapter2.concat₂''`.
Each step appends the accumulator (which keeps growing) onto the next block, so
the accumulator length is what gets charged. -/
def concat₂ {a : Type} : List (List a) → List a → Prog (ConcatOp a) (List a)
  | [],        acc => pure acc
  | xs :: xss, acc => do
      let acc' ← lift (ConcatOp.app acc xs)
      concat₂ xss acc'

/-- if `xss` is a list of `m` lists each of length `n`, then `concat₁` is
`Θ(m * n)`. Query-model analogue of `Chapter2.concat₁''_time`. -/
theorem concat₁_runtime {a : Type} (xss : List (List a))
    (n : Nat) (h : ∀ xs ∈ xss, xs.length = n) :
    (concat₁ xss).runtime concatCost = xss.length * n := by
  induction xss with
  | nil => simp [concat₁]
  | cons xs xss' ih =>
      have h₁ : xs.length = n := h xs List.mem_cons_self
      have h₂ : ∀ ys ∈ xss', ys.length = n :=
        fun ys hys => h ys (List.mem_cons_of_mem xs hys)
      simp only [concat₁, Prog.bind_eq, Prog.runtime_bind, Prog.runtime_lift,
        concatCost_cost, List.length_cons, ih h₂, h₁]
      ring

/-- The result of `concat₁` really is the concatenation (it does not cheat). -/
@[simp] theorem concat₁_result {a : Type} (xss : List (List a)) :
    (concat₁ xss).result concatCost = xss.flatten := by
  induction xss with
  | nil => rfl
  | cons xs xss' ih => simp [concat₁, ih]

/-- Cost of the left-associated fold: `concat₂` over `m` blocks of length `n`
starting from an accumulator of length `a₀` costs `a₀ * m + n * m * (m-1) / 2`.
We state it in the doubled, subtraction-free form used in
`Chapter2.concat₂'_time`: it is `Θ(m² * n)`. -/
theorem concat₂_runtime {a : Type} (xss : List (List a))
    (n : Nat) (h : ∀ xs ∈ xss, xs.length = n)
    (acc : List a) :
    (2 * (concat₂ xss acc).runtime concatCost : Int)
      = 2 * acc.length * xss.length + n * xss.length * (xss.length - 1) := by
  induction xss generalizing acc with
  | nil => simp [concat₂]
  | cons xs xss' ih =>
      have h₁ : xs.length = n := h xs List.mem_cons_self
      have h₂ : ∀ ys ∈ xss', ys.length = n :=
        fun ys hys => h ys (List.mem_cons_of_mem xs hys)
      -- one fold step charges the current accumulator length, then recurses on
      -- the (grown) accumulator
      have hstep : (concat₂ (xs :: xss') acc).runtime concatCost
          = acc.length + (concat₂ xss' (acc ++ xs)).runtime concatCost := by
        simp [concat₂]
      have hIH := ih h₂ (acc ++ xs)
      rw [List.length_append, h₁] at hIH
      rw [hstep, List.length_cons]
      push_cast at hIH ⊢
      linear_combination hIH


/-! ## Practical comparison

The pay-off of the query model over `TimeM`: the *same* program is measured
under different cost models, with no change to the algorithm. Under `TimeM`
each of these would need a separately-written function.

`.eval` returns the `(result, cost)` pair; `.result`/`.runtime` project them. -/

-- `append` costs one per element under `stepCost`, two under `stepCost2`,
-- but computes the same list either way:
#eval (append [1, 2, 3] [4, 5]).eval stepCost    -- ([1,2,3,4,5], 3)
#eval (append [1, 2, 3] [4, 5]).eval stepCost2   -- ([1,2,3,4,5], 6)

-- On 4 blocks of length 2, the right fold `concat₁` is Θ(m·n) = 4·2 = 8,
-- while the left fold `concat₂` is Θ(m²·n) = 0+2+4+6 = 12 — same result,
-- different cost, exposed purely by the model:
#eval (concat₁ [[1, 2], [3, 4], [5, 6], [7, 8]]).eval concatCost      -- (…, 8)
#eval (concat₂ [[1, 2], [3, 4], [5, 6], [7, 8]] []).eval concatCost   -- (…, 12)

-- the theorem, specialised: m = 4 blocks of length n = 2
example : (concat₁ [[1, 2], [3, 4], [5, 6], [7, 8]]).runtime concatCost = 4 * 2 :=
  concat₁_runtime _ 2 (by decide)

end Chapter2Query
