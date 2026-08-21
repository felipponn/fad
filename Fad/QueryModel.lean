/-
Query model (free-monad) for reasoning about algorithm complexity.

This is a small, self-contained reimplementation of the *query model*
described in `query-model-tutorial.md` (CSLib PR #372, still open at the
pinned `cslib` revision, so it is vendored here instead of imported).

The point of this module is to offer an alternative to `TimeM`
(`Cslib.Algorithms.Lean.TimeM`, used in `Fad.Chapter2`): instead of a
computation that *carries* a running cost, an algorithm is a *tree of
queries* (`Prog`) whose cost is assigned afterwards by a `Model`. The same
program can then be measured under several models, and the algorithm can
never "cheat" by inspecting the cost.

See `Fad.Chapter2Query` for a side-by-side comparison with the `TimeM`
versions of `append`/`concat` from `Fad.Chapter2`.
-/

import Mathlib.Tactic

set_option autoImplicit false

namespace QueryModel

universe u

/-- A program that issues queries of type `Q` and returns an `R`.

Internally a free monad: a tree whose leaves are `pure` results and whose
internal nodes are queries `Q ι` together with a continuation `ι → Prog Q R`
that consumes the (not-yet-known) answer. Nothing runs until `eval`. -/
inductive Prog (Q : Type → Type u) (R : Type) : Type (max u 1) where
  | pure  : R → Prog Q R
  | query : {ι : Type} → Q ι → (ι → Prog Q R) → Prog Q R

namespace Prog

variable {Q : Type → Type u} {R α β : Type}

/-- Lift a single query into a one-node program. -/
@[inline] def lift {ι : Type} (q : Q ι) : Prog Q ι :=
  .query q .pure

def bind : Prog Q α → (α → Prog Q β) → Prog Q β
  | .pure a,    f => f a
  | .query q k, f => .query q (fun i => bind (k i) f)

instance : Monad (Prog Q) where
  pure := .pure
  bind := bind

@[simp] theorem pure_eq (a : α) : (Pure.pure a : Prog Q α) = .pure a := rfl
@[simp] theorem bind_eq (m : Prog Q α) (f : α → Prog Q β) :
    (m >>= f) = bind m f := rfl

@[simp] theorem bind_pure (a : α) (f : α → Prog Q β) :
    bind (.pure a) f = f a := rfl
@[simp] theorem bind_query {ι} (q : Q ι) (k : ι → Prog Q α) (f : α → Prog Q β) :
    bind (.query q k) f = .query q (fun i => bind (k i) f) := rfl

/-- A model gives meaning to a `Prog`: how to answer each query, and how much
each query costs. `Cost` is any additive-monoid-like type (`Nat`, a trace,
…). -/
structure _root_.QueryModel.Model (Q : Type → Type u) (Cost : Type) where
  evalQuery : {ι : Type} → Q ι → ι
  cost      : {ι : Type} → Q ι → Cost

/-- Run a program against a model, returning the result and the accumulated
cost. At each query node the model supplies the answer (choosing the branch)
*and* the cost, which is summed along the followed path. -/
def eval {Cost : Type} [Add Cost] [Zero Cost] :
    Prog Q R → Model Q Cost → R × Cost
  | .pure r,    _ => (r, 0)
  | .query q k, m =>
      let i := m.evalQuery q
      let (r, c) := eval (k i) m
      (r, m.cost q + c)

/-- The result of `eval` (ignoring cost). Deliberately *not* `@[simp]`: we let
the `result_*` lemmas below drive simplification, otherwise simp would unfold
`result` to `(eval …).1` before the structural `result_bind` lemma can fire. -/
def result {Cost : Type} [Add Cost] [Zero Cost]
    (p : Prog Q R) (m : Model Q Cost) : R := (p.eval m).1

/-- The cost of `eval` (ignoring result). Not `@[simp]` for the same reason as
`result`; the `runtime_*` lemmas are the simp normal form. -/
def runtime {Cost : Type} [Add Cost] [Zero Cost]
    (p : Prog Q R) (m : Model Q Cost) : Cost := (p.eval m).2

@[simp] theorem eval_pure {Cost : Type} [Add Cost] [Zero Cost]
    (r : R) (m : Model Q Cost) : (Prog.pure r).eval m = (r, 0) := rfl

@[simp] theorem eval_query {Cost : Type} [Add Cost] [Zero Cost]
    {ι} (q : Q ι) (k : ι → Prog Q R) (m : Model Q Cost) :
    (Prog.query q k).eval m
      = (((k (m.evalQuery q)).eval m).1,
         m.cost q + ((k (m.evalQuery q)).eval m).2) := rfl

@[simp] theorem result_pure {Cost : Type} [Add Cost] [Zero Cost]
    (r : R) (m : Model Q Cost) : (Prog.pure r).result m = r := rfl
@[simp] theorem runtime_pure {Cost : Type} [Add Cost] [Zero Cost]
    (r : R) (m : Model Q Cost) : (Prog.pure r).runtime m = 0 := rfl

@[simp] theorem result_lift {Cost : Type} [Add Cost] [Zero Cost]
    {ι} (q : Q ι) (m : Model Q Cost) : (Prog.lift q).result m = m.evalQuery q := rfl
@[simp] theorem runtime_lift {Cost : Type} [AddZeroClass Cost]
    {ι} (q : Q ι) (m : Model Q Cost) : (Prog.lift q).runtime m = m.cost q := by
  simp [Prog.lift, Prog.runtime, eval]

/-- Cost accumulates additively across a `bind`: the cost of the whole is the
cost of the first program plus the cost of the continuation applied to its
result. This is the query-model analogue of `TimeM.time_of_bind`, and the key
lemma that makes complexity proofs go through by structural induction. -/
theorem eval_bind {Cost : Type} [AddMonoid Cost]
    (p : Prog Q α) (f : α → Prog Q β) (m : Model Q Cost) :
    (Prog.bind p f).eval m
      = (((f (p.result m)).eval m).1,
         (p.runtime m) + ((f (p.result m)).eval m).2) := by
  induction p with
  | pure a => simp [Prog.bind, Prog.result, Prog.runtime, eval]
  | query q k ih =>
      simp only [Prog.bind_query, eval_query, Prog.result, Prog.runtime, ih]
      exact Prod.ext rfl (add_assoc _ _ _).symm

@[simp] theorem result_bind {Cost : Type} [AddMonoid Cost]
    (p : Prog Q α) (f : α → Prog Q β) (m : Model Q Cost) :
    (Prog.bind p f).result m = (f (p.result m)).result m := by
  simp [Prog.result, eval_bind]

@[simp] theorem runtime_bind {Cost : Type} [AddMonoid Cost]
    (p : Prog Q α) (f : α → Prog Q β) (m : Model Q Cost) :
    (Prog.bind p f).runtime m = p.runtime m + (f (p.result m)).runtime m := by
  simp [Prog.runtime, eval_bind]

end Prog

/-- Upper bound: some constant `k` bounds the cost by `k * bound n` for every
input of size at most `n`. Mirrors the definition in the tutorial. -/
def UpperBound {Q : Type → Type u} {α β : Type}
    (prog  : α → Prog Q β)
    (model : Model Q Nat)
    (size  : α → Nat)
    (bound : Nat → Nat) : Prop :=
  ∃ k, ∀ n x, size x ≤ n → (prog x).runtime model ≤ k * bound n

/-- Lower bound: for every `n` there is an input of that size forcing at least
`bound n` cost. -/
def LowerBound {Q : Type → Type u} {α β : Type}
    (prog  : α → Prog Q β)
    (model : Model Q Nat)
    (size  : α → Nat)
    (bound : Nat → Nat) : Prop :=
  ∀ n, ∃ x, size x = n ∧ (prog x).runtime model ≥ bound n

end QueryModel
