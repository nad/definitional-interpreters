------------------------------------------------------------------------
-- Pointers to results from the paper
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module README.Pointers-to-results-from-the-paper where

import Colist
import Conat
import Omniscience

import Delay-monad
import Delay-monad.Bisimilarity
import Delay-monad.Monad
import Delay-monad.Quantitative-weak-bisimilarity

import Only-allocation
import Unbounded-space
import Upper-bounds

import Lambda.Compiler
import Lambda.Compiler-correctness
import Lambda.Compiler-correctness.Sizes-match
import Lambda.Compiler-correctness.Steps-match
import Lambda.Delay-crash
import Lambda.Delay-crash-trace
import Lambda.Interpreter
import Lambda.Interpreter.Stack-sizes
import Lambda.Interpreter.Stack-sizes.Counterexample
import Lambda.Interpreter.Stack-sizes.Example
import Lambda.Interpreter.Steps
import Lambda.Interpreter.Steps.Counterexample
import Lambda.Virtual-machine
import Lambda.Virtual-machine.Instructions
import Lambda.Syntax

------------------------------------------------------------------------
-- Section 2

-- Conatural numbers.

Conat  = Conat.Conat
Conat′ = Conat.Conat′

-- Infinity.

infinity = Conat.infinity

-- Ordering.

[_]_≤_  = Conat.[_]_≤_
[_]_≤′_ = Conat.[_]_≤′_

-- Bisimilarity.

[_]_∼N_ = Conat.[_]_∼_

------------------------------------------------------------------------
-- Section 3

-- Programs.

Stmt    = Only-allocation.Stmt
Program = Only-allocation.Program

-- Colists.

Colist = Colist.Colist

-- The interpreter.

modify = Unbounded-space.modify
⟦_⟧₁   = Unbounded-space.⟦_⟧
⟦_⟧′   = Unbounded-space.⟦_⟧′

-- Upper bounds.

[_]_⊑_  = Upper-bounds.[_]_⊑_
[_]_⊑′_ = Upper-bounds.[_]_⊑′_

-- The □ predicate.

□ = Colist.□

-- Least upper bounds.

LUB = Upper-bounds.LUB

-- Least upper bounds are unique up to bisimilarity.

lub-unique = Upper-bounds.lub-unique

-- Antisymmetry for conatural numbers.

antisymmetric = Conat.antisymmetric-≤

-- WLPO.

WLPO = Omniscience.WLPO

-- WLPO is classically valid: it follows from excluded middle and
-- extensionality for functions.

LEM→WLPO = Omniscience.LEM→WLPO

-- WLPO is logically equivalent to one formulation of "least upper
-- bounds exist for every colist".

wlpo⇔lub = Unbounded-space.wlpo⇔lub

-- Maximum heap usage.

Heap-usage = Unbounded-space.Heap-usage

-- This was not mentioned in the paper, but WLPO is also logically
-- equivalent to one formulation of "maximum heap usages exist for
-- every program".

wlpo⇔max = Unbounded-space.wlpo⇔max

-- The maximum heap usage is unique up to bisimilarity.

max-unique = Unbounded-space.max-unique

-- Some examples.

bounded   = Only-allocation.bounded
bounded₂  = Only-allocation.bounded₂
unbounded = Only-allocation.unbounded
_∷′_      = Colist._∷′_

-- The example programs have infinitely long traces.

bounded-loops   = Unbounded-space.bounded-loops
bounded₂-loops  = Unbounded-space.bounded₂-loops
unbounded-loops = Unbounded-space.unbounded-loops

-- Properties showing that the example programs have certain maximum
-- heap usages.

max-bounded-1   = Unbounded-space.max-bounded-1
max-bounded₂-2  = Unbounded-space.max-bounded₂-2
max-unbounded-∞ = Unbounded-space.max-unbounded-∞

-- If no natural number is an upper bound of the heap usage of p, then
-- the maximum heap usage of p is infinity.

no-finite-max→infinite-max = Unbounded-space.no-finite-max→infinite-max

-- If no natural number is an upper bound of ms, but the conatural
-- number m is, then m is bisimilar to infinity.

no-finite→infinite = Upper-bounds.no-finite→infinite

------------------------------------------------------------------------
-- Section 4

-- The optimiser.

opt = Unbounded-space.opt

-- The optimiser improves the space complexity of at least one
-- program.

opt-improves = Unbounded-space.opt-improves

-- The semantics of optimise bounded-space₂ matches that of
-- bounded-space.

opt-bounded₂∼bounded = Unbounded-space.opt-bounded₂∼bounded

-- Bisimilarity of colists.

[_]_∼L_ = Colist.[_]_∼_

-- The maximum heap usage of an optimised program is at most as high
-- as that of the original program (assuming that these maximums
-- exist).

opt-correct = Unbounded-space.opt-correct

-- The [_]_≲_ relation.

[_]_≲_  = Upper-bounds.[_]_≲_
[_]_≲′_ = Upper-bounds.[_]_≲′_

-- If ms has the least upper bound m, and ns has the least upper bound
-- n, then ms is bounded by ns if and only if m is bounded by n.

≲⇔least-upper-bounds-≤ = Upper-bounds.≲⇔least-upper-bounds-≤

-- Four combinators that can be used to prove that one colist is
-- bounded by another.

[]≲     = Upper-bounds.[]≲
consʳ-≲ = Upper-bounds.consʳ-≲
consˡ-≲ = Upper-bounds.consˡ-≲
cons′-≲ = Upper-bounds.cons′-≲
Bounded = Upper-bounds.Bounded

-- If consʳ-≲ had taken the primed variant of the relation as an
-- argument instead, then one could have proved that any colist was
-- bounded by any infinite colist, and this leads to a contradiction.

consʳ-≲′→≲-infinite = Upper-bounds.consʳ-≲′→≲-infinite
¬-consʳ-≲′          = Upper-bounds.¬-consʳ-≲′

-- The [_]_≲_ relation is a preorder. (The transitivity result has a
-- type signature that differs slightly from that given in the paper.)

reflexive-≲  = Upper-bounds._□≲
transitive-≲ = Upper-bounds.step-≲

-- Transitivity cannot be made size-preserving in the second argument.

¬-transitivity-size-preservingʳ =
  Upper-bounds.¬-transitivity-size-preservingʳ

-- A size-preserving variant of transitivity. (This result has a
-- type signature that differs slightly from that given in the paper.)

transitive-∼≲ = Upper-bounds.step-∼≲

-- The main lemma used to prove that the maximum heap usage of an
-- optimised program is at most as high as that of the original
-- program (assuming that these maximums exist).

opt-correct-≲ = Unbounded-space.opt-correct-≲

------------------------------------------------------------------------
-- Section 5

-- The delay monad.

Delay = Delay-monad.Delay

-- The non-terminating computation never.

never = Delay-monad.never

-- Monad instance.

monad-instance₁ = Delay-monad.Monad.delay-raw-monad

-- Strong bisimilarity.

[_]_∼D_ = Delay-monad.Bisimilarity.[_]_∼_

-- Monad laws.

left-identity₁  = Delay-monad.Monad.left-identity′
right-identity₁ = Delay-monad.Monad.right-identity′
associativity₁  = Delay-monad.Monad.associativity′

-- Weak bisimilarity. (This relation is not defined in exactly the
-- same way as in the paper.)

[_]_≈D_ = Delay-monad.Bisimilarity.[_]_≈_

------------------------------------------------------------------------
-- Section 6

-- Terms.

Tm = Lambda.Syntax.Tm

-- Environments and values. (The code uses a definition which is
-- parametrised by the type of terms. The same definition is used also
-- for virtual machine environments and values.)

Env   = Lambda.Syntax.Closure.Env
Value = Lambda.Syntax.Closure.Value

-- DelayC (called Delay-crash in the code) and crash.

DelayC = Lambda.Delay-crash.Delay-crash
crash  = Lambda.Delay-crash.crash

-- The computation crash (in fact, any computation of the form now x)
-- is not weakly bisimilar to never.

now≉never = Delay-monad.Bisimilarity.now≉never

-- The interpreter.

_∙_  = Lambda.Interpreter._∙_
⟦_⟧₂ = Lambda.Interpreter.⟦_⟧
⟦if⟧ = Lambda.Interpreter.⟦if⟧

------------------------------------------------------------------------
-- Section 7

-- DelayCT (called Delay-crash-trace in the code).

DelayCT = Lambda.Delay-crash-trace.Delay-crash-trace
trace   = Lambda.Delay-crash-trace.trace
delayC  = Lambda.Delay-crash-trace.delay-crash

-- Monad instance.

monad-instance₂ = Lambda.Delay-crash-trace.raw-monad

-- Strong bisimilarity.

[_]_∼DCT_ = Lambda.Delay-crash-trace.[_]_∼_

-- Monad laws.

left-identity₂  = Lambda.Delay-crash-trace.left-identity
right-identity₂ = Lambda.Delay-crash-trace.right-identity
associativity₂  = Lambda.Delay-crash-trace.associativity

-- Instructions and code.

Instr = Lambda.Virtual-machine.Instructions.Instr
Code  = Lambda.Virtual-machine.Instructions.Code

-- Environments and values. (The code uses a definition which is
-- parametrised by the type of terms. The same definition is used also
-- for the interpreter's environments and values.)

VM-Env   = Lambda.Syntax.Closure.Env
VM-Value = Lambda.Syntax.Closure.Value

-- Stack elements and stacks.

Stack-element = Lambda.Virtual-machine.Instructions.Stack-element
Stack         = Lambda.Virtual-machine.Instructions.Stack

-- States.

State = Lambda.Virtual-machine.Instructions.State

-- The virtual machine.

Result      = Lambda.Virtual-machine.Instructions.Result
step        = Lambda.Virtual-machine.step
exec⁺       = Lambda.Virtual-machine.exec⁺
exec⁺′      = Lambda.Virtual-machine.exec⁺′
exec        = Lambda.Virtual-machine.exec
stack-sizes = Lambda.Virtual-machine.stack-sizes

------------------------------------------------------------------------
-- Section 8

-- Tail context information.

In-tail-context = Lambda.Compiler.In-tail-context

-- The compilation functions.

comp      = Lambda.Compiler.comp
comp-body = Lambda.Compiler.comp-body
comp-name = Lambda.Compiler.comp-name
comp-env  = Lambda.Compiler.comp-env
comp-val  = Lambda.Compiler.comp-val
comp₀     = Lambda.Compiler.comp₀

-- Compiler correctness.

compiler-correct = Lambda.Compiler-correctness.correct

-- The key lemma used to prove compiler correctness.

key-lemma₁ = Lambda.Compiler-correctness.⟦⟧-correct
Cont-OK    = Lambda.Compiler-correctness.Cont-OK
Stack-OK   = Lambda.Compiler-correctness.Stack-OK

------------------------------------------------------------------------
-- Section 9

-- The instrumented interpreter.

[_,_]_∙S_    = Lambda.Interpreter.Stack-sizes.[_,_]_∙_
⟦_⟧S         = Lambda.Interpreter.Stack-sizes.⟦_⟧
δ            = Lambda.Interpreter.Stack-sizes.δ
⟦if⟧S        = Lambda.Interpreter.Stack-sizes.⟦if⟧
scanl        = Colist.scanl
numbers      = Lambda.Interpreter.Stack-sizes.numbers
stack-sizesS = Lambda.Interpreter.Stack-sizes.stack-sizes

-- The instrumented semantics produces computations that are strongly
-- bisimilar to those produced by the other semantics.

⟦⟧∼⟦⟧ = Lambda.Interpreter.Stack-sizes.⟦⟧∼⟦⟧

-- If the trace of stack sizes produced by the instrumented semantics
-- has the least upper bound i, and the corresponding trace produced
-- by the virtual machine has the least upper bound v, then i and v
-- are bisimilar.

maximum-stack-sizes-match =
  Lambda.Compiler-correctness.Sizes-match.maximum-stack-sizes-match

-- The trace of stack sizes produced by the virtual machine is not
-- necessarily bisimilar to that produced by the instrumented
-- interpreter.

stack-sizes-not-bisimilar =
  Lambda.Interpreter.Stack-sizes.Counterexample.stack-sizes-not-bisimilar

-- The trace of stack sizes produced by the virtual machine and that
-- produced by the instrumented interpreter are upper bounds of each
-- other.

stack-sizes-related =
  Lambda.Compiler-correctness.Sizes-match.stack-sizes-related

-- The [_]_≂_ relation.

[_]_≂_  = Upper-bounds.[_]_≂_
[_]_≂′_ = Upper-bounds.[_]_≂′_

-- Colists that are related by this relation have the same least upper
-- bounds (if any).

LUB-cong = Upper-bounds.LUB-cong

-- Some combinators that can be used to prove that two colists are
-- bounded by each other.

consʳ-≂ = Upper-bounds.consʳ-≂
consˡ-≂ = Upper-bounds.consˡ-≂
cons-≂  = Upper-bounds.cons-≂
cons′-≂ = Upper-bounds.cons′-≂

-- The [_]_≂_ relation is an equivalence relation. (The
-- transitivity-like results have type signatures that differ slightly
-- from those given in the paper.)

reflexive-≂   = Upper-bounds._□≂
symmetric-≂   = Upper-bounds.symmetric-≂
transitive-≂  = Upper-bounds.step-≂
transitive-∼≂ = Upper-bounds.step-∼≂
transitive-≂∼ = Upper-bounds.step-≂∼

-- The [_]_≂″_ relation.

[_]_≂″_ = Upper-bounds.[_]_≂″_

-- [_]_≂′_ and [_]_≂″_ are pointwise logically equivalent.

≂′⇔≂″ = Upper-bounds.≂′⇔≂″

-- This was not mentioned in the paper, but a corresponding relation
-- can also be defined for [_]_≲′_.

[_]_≲″_ = Upper-bounds.[_]_≲″_
≲′⇔≲″   = Upper-bounds.≲′⇔≲″

-- The key lemma used to prove correctness.

key-lemma₂ = Lambda.Compiler-correctness.Sizes-match.⟦⟧-correct

-- A non-terminating program that requires unbounded stack space.

Ω                          = Lambda.Syntax.Ω
Ω-loops                    = Lambda.Interpreter.Ω-loops′
Ω-requires-unbounded-space =
  Lambda.Interpreter.Stack-sizes.Ω-requires-unbounded-space

-- A non-terminating program that runs in bounded stack space.

go               = Lambda.Interpreter.Stack-sizes.Example.go
go-loops         = Lambda.Interpreter.Stack-sizes.Example.go-loops
go-bounded-stack =
  Lambda.Interpreter.Stack-sizes.Example.go-bounded-stack

------------------------------------------------------------------------
-- Section 10

-- The uninstrumented interpreter does not provide a suitable cost
-- measure, in the sense that there is a family of programs for which
-- the running "time" (number of steps) of the corresponding compiled
-- programs on the virtual machine is not linear in the running time
-- on the interpreter.

not-suitable-cost-measure =
  Lambda.Interpreter.Steps.Counterexample.not-suitable-cost-measure

-- The instrumented interpreter.

✓_    = Lambda.Interpreter.Steps.✓_
_∙T_  = Lambda.Interpreter.Steps._∙_
⟦_⟧T  = Lambda.Interpreter.Steps.⟦_⟧
⟦if⟧T = Lambda.Interpreter.Steps.⟦if⟧

-- The cost measure provided by the instrumented interpreter is
-- "suitable", in the sense that the cost of running a compiled
-- program on the virtual machine is linear in the cost of running the
-- corresponding source program on the interpreter, and vice versa.

the-cost-measure-is-suitable =
  Lambda.Compiler-correctness.Steps-match.steps-match

-- Quantitative weak bisimilarity.

[_∣_∣_∣_∣_]_≈D_ =
  Delay-monad.Quantitative-weak-bisimilarity.[_∣_∣_∣_∣_]_≈_

-- A characterisation of quantitative weak bisimilarity.

≈⇔≈×steps≤steps² =
  Delay-monad.Quantitative-weak-bisimilarity.≈⇔≈×steps≤steps²

-- The left-to-right direction of the characterisation can be made
-- size-preserving.

≈→≈×steps≤steps² =
  Delay-monad.Quantitative-weak-bisimilarity.≈→≈×steps≤steps²

-- The right-to-left direction of the characterisation can be made
-- size-preserving if and only if the carrier type is uninhabited
-- (assuming that Agda is not buggy).

≈×steps≤steps²→≈⇔uninhabited =
  Delay-monad.Quantitative-weak-bisimilarity.≈×steps≤steps²→≈⇔uninhabited

-- Weakening.

weaken = Delay-monad.Quantitative-weak-bisimilarity.weaken

-- Two transitivity-like results.

transitive-≳∼ = Delay-monad.Quantitative-weak-bisimilarity.transitive-≳∼
transitive-≈∼ = Delay-monad.Quantitative-weak-bisimilarity.transitive-≈∼
transitive-∼≈ = Delay-monad.Quantitative-weak-bisimilarity.transitive-∼≈

-- The key lemma used to prove that the cost measure is "suitable".

key-lemma₃ = Lambda.Compiler-correctness.Steps-match.⟦⟧-correct
