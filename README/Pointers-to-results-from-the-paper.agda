------------------------------------------------------------------------
-- Pointers to results from the paper
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Pointers-to-results-from-the-paper where

import Colist
import Conat
import Nat
import Omniscience
import Prelude

import Delay-monad
import Delay-monad.Bisimilarity
import Delay-monad.Monad

import Bounded-space
import Only-allocation
import Unbounded-space
import Upper-bounds

import Lambda.Compiler
import Lambda.Compiler-correctness
import Lambda.Compiler-correctness.Sizes-match
import Lambda.Delay-crash
import Lambda.Delay-crash-trace
import Lambda.Interpreter
import Lambda.Interpreter.Instrumented
import Lambda.Interpreter.Instrumented.Counterexample
import Lambda.Interpreter.Instrumented.Example
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

[_]_∼N_  = Conat.[_]_∼_
[_]_∼N′_ = Conat.[_]_∼′_

------------------------------------------------------------------------
-- Section 3

-- The delay monad.

Delay  = Delay-monad.Delay
Delay′ = Delay-monad.Delay′

-- The non-terminating computation never.

never = Delay-monad.never

-- Monadic combinators. (These combinators are not defined in exactly
-- the same way as in the paper.)

monad-instance = Delay-monad.Monad.delay-raw-monad

-- Strong and weak bisimilarity. (These relations are not defined in
-- exactly the same way as in the paper.)

[_]_∼D_ = Delay-monad.Bisimilarity.[_]_∼_
[_]_≈D_ = Delay-monad.Bisimilarity.[_]_≈_

------------------------------------------------------------------------
-- Section 4

-- Programs.

Stmt    = Only-allocation.Stmt
Program = Only-allocation.Program

-- Colists.

Colist  = Colist.Colist
Colist′ = Colist.Colist′

-- Heaps.

Heap = Bounded-space.Heap

-- A proof-producing comparison operator.

_⊎_   = Prelude._⊎_
_≤_   = Nat._≤_
_<_   = Nat._<_
_≤⊎>_ = Nat._≤⊎>_

-- Heap operations.

shrink = Bounded-space.shrink
Maybe  = Prelude.Maybe
grow   = Bounded-space.grow

-- The interpreter.

step₁  = Bounded-space.step
⟦_⟧₁   = Bounded-space.⟦_⟧
crash₁ = Bounded-space.crash

-- The computation now x is not weakly bisimilar to never.

¬_        = Prelude.¬_
now≉never = Delay-monad.Bisimilarity.now≉never

-- Some examples.

constant-space  = Only-allocation.constant-space
constant-space₂ = Only-allocation.constant-space₂
unbounded-space = Only-allocation.unbounded-space
_∷′_            = Colist._∷′_

-- Some properties about the examples.

constant-space-crash  = Bounded-space.constant-space-crash
constant-space-loop   = Bounded-space.constant-space-loop
constant-space₂-loop  = Bounded-space.constant-space₂-loop
unbounded-space-crash = Bounded-space.unbounded-space-crash

-- The _≃_ relation. (Unlike in the paper this relation is sized.)

∃   = Prelude.∃
_≃_ = Bounded-space.[_]_≃_

-- The _≃_ relation is an equivalence relation.

reflexive-≃  = Bounded-space.reflexive
symmetric-≃  = Bounded-space.symmetric
transitive-≃ = Bounded-space.transitive

-- The _≃_ relation is preserved by the cons operator.

∷-cong = Bounded-space.∷-cong

-- The _≃_ relation relates constant-space and constant-space₂, but
-- not constant-space and unbounded-space.

constant-space≃constant-space₂ =
  Bounded-space.constant-space≃constant-space₂
¬constant-space≃unbounded-space =
  Bounded-space.¬constant-space≃unbounded-space

------------------------------------------------------------------------
-- Section 5

-- The interpreter.

modify = Unbounded-space.modify
⟦_⟧₂   = Unbounded-space.⟦_⟧
⟦_⟧′   = Unbounded-space.⟦_⟧′

-- Upper bounds.

[_]_⊑_  = Upper-bounds.[_]_⊑_
[_]_⊑′_ = Upper-bounds.[_]_⊑′_

-- The □ predicate.

□  = Colist.□
□′ = Colist.□′

-- Least upper bounds.

LUB = Upper-bounds.LUB

-- Least upper bounds are unique up to bisimilarity.

lub-unique = Upper-bounds.lub-unique

-- Antisymmetry for conatural numbers.

antisymmetric = Conat.antisymmetric-≤

-- Maximum heap usage.

Maximum-heap-usage = Unbounded-space.Maximum-heap-usage

-- Maximum heap usage is unique up to bisimilarity.

max-unique = Unbounded-space.max-unique

-- The example programs have infinitely long traces.

constant-space-loops  = Unbounded-space.constant-space-loops
constant-space₂-loops = Unbounded-space.constant-space₂-loops
unbounded-space-loops = Unbounded-space.unbounded-space-loops

-- Properties showing that the example programs have certain maximum
-- heap usages.

max-constant-space-1  = Unbounded-space.max-constant-space-1
max-constant-space₂-2 = Unbounded-space.max-constant-space₂-2
max-unbounded-space-∞ = Unbounded-space.max-unbounded-space-∞

-- If no natural number is an upper bound of the heap usage of p, then
-- the maximum heap usage of p is infinity.

no-finite-max→infinite-max = Unbounded-space.no-finite-max→infinite-max

-- If no natural number is an upper bound of ms, but the conatural
-- number m is, then m is bisimilar to infinity.

no-finite→infinite = Upper-bounds.no-finite→infinite

------------------------------------------------------------------------
-- Section 6

-- If the maximum heap usage could always be computed (in a certain
-- sense), then WLPO would hold.

max→wlpo = Unbounded-space.max→wlpo

-- Dec and WLPO.

Dec  = Prelude.Dec
WLPO = Omniscience.WLPO

-- WLPO follows from excluded middle and extensionality for functions.

LEM→WLPO = Omniscience.LEM→WLPO

-- If WLPO holds, then the least upper bound of a colist of natural
-- numbers can be determined.

wlpo→lub = Upper-bounds.wlpo→lub

-- WLPO is logically equivalent to both of the computability
-- statements for maximum heap usages and least upper bounds.

wlpo⇔max = Unbounded-space.wlpo⇔max
wlpo⇔lub = Unbounded-space.wlpo⇔lub

------------------------------------------------------------------------
-- Section 7

-- The optimiser.

optimise = Unbounded-space.optimise

-- The optimiser improves the space complexity of at least one
-- program.

optimise-improves = Unbounded-space.optimise-improves

-- The semantics of optimise constant-space₂ matches that of
-- constant-space.

optimise-constant-space₂∼constant-space =
  Unbounded-space.optimise-constant-space₂∼constant-space

-- Bisimilarity of colists.

[_]_∼L_ = Colist.[_]_∼_

-- The maximum heap usage of an optimised program is at most as high
-- as that of the original program (assuming that these maximums
-- exist).

optimise-correct = Unbounded-space.optimise-correct

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

optimise-correct-≲ = Unbounded-space.optimise-correct-≲

------------------------------------------------------------------------
-- Section 8

-- Terms.

Tm = Lambda.Syntax.Tm

-- Environments and values. (The code uses a definition which is
-- parametrised by the type of terms. The same definition is used also
-- for virtual machine environments and values.)

Env   = Lambda.Syntax.Closure.Env
Value = Lambda.Syntax.Closure.Value

-- Delay-crash and crash.

Delay-crash = Lambda.Delay-crash.Delay-crash
crash₂      = Lambda.Delay-crash.crash

-- The interpreter.

_∙_  = Lambda.Interpreter._∙_
⟦_⟧₃ = Lambda.Interpreter.⟦_⟧
⟦if⟧ = Lambda.Interpreter.⟦if⟧

------------------------------------------------------------------------
-- Section 9

-- Delay-crash-trace.

Delay-crash-trace  = Lambda.Delay-crash-trace.Delay-crash-trace
Delay-crash-trace′ = Lambda.Delay-crash-trace.Delay-crash-trace′
trace              = Lambda.Delay-crash-trace.trace
delay-crash        = Lambda.Delay-crash-trace.delay-crash

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
step₂       = Lambda.Virtual-machine.step
exec⁺       = Lambda.Virtual-machine.exec⁺
exec⁺′      = Lambda.Virtual-machine.exec⁺′
exec        = Lambda.Virtual-machine.exec
stack-size  = Lambda.Virtual-machine.Instructions.stack-size
stack-sizes = Lambda.Virtual-machine.stack-sizes

------------------------------------------------------------------------
-- Section 10

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
Cont-OK₁   = Lambda.Compiler-correctness.Cont-OK
Stack-OK₁  = Lambda.Compiler-correctness.Stack-OK

------------------------------------------------------------------------
-- Section 11

-- The instrumented interpreter.

[_,_]_∙I_    = Lambda.Interpreter.Instrumented.[_,_]_∙_
⟦_⟧I         = Lambda.Interpreter.Instrumented.⟦_⟧
δ₁           = Lambda.Interpreter.Instrumented.δ₁
δ₂           = Lambda.Interpreter.Instrumented.δ₂
⟦if⟧I        = Lambda.Interpreter.Instrumented.⟦if⟧
scanl        = Colist.scanl
numbers      = Lambda.Interpreter.Instrumented.numbers
stack-sizesI = Lambda.Interpreter.Instrumented.stack-sizes

-- The instrumented semantics produces computations that are strongly
-- bisimilar to those produced by the other semantics.

⟦⟧∼⟦⟧ = Lambda.Interpreter.Instrumented.⟦⟧∼⟦⟧

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
  Lambda.Interpreter.Instrumented.Counterexample.stack-sizes-not-bisimilar

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

-- The key lemma used to prove correctness.

key-lemma₂ = Lambda.Compiler-correctness.Sizes-match.⟦⟧-correct
Cont-OK₂   = Lambda.Compiler-correctness.Sizes-match.Cont-OK
Stack-OK₂  = Lambda.Compiler-correctness.Sizes-match.Stack-OK

------------------------------------------------------------------------
-- Section 12

-- Ω and ω.

ω = Lambda.Syntax.ω
Ω = Lambda.Syntax.Ω

-- Ω is non-terminating.

Ω-loops = Lambda.Interpreter.Ω-loops′

-- Ω-sizes.

Ω-sizes = Lambda.Interpreter.Instrumented.Ω-sizes

-- Ω-sizes 0 matches the stack-sizes encountered when interpreting Ω.

stack-sizes-Ω∼Ω-sizes-0 =
  Lambda.Interpreter.Instrumented.stack-sizes-Ω∼Ω-sizes-0

-- The least upper bound of Ω-sizes 0 is infinity.

lub-Ω-sizes-0-infinity =
  Lambda.Interpreter.Instrumented.lub-Ω-sizes-0-infinity

-- Ω does not run in bounded stack space.

Ω-requires-unbounded-space =
  Lambda.Interpreter.Instrumented.Ω-requires-unbounded-space

-- The implementations of def and go.

def = Lambda.Interpreter.Instrumented.Example.def
go  = Lambda.Interpreter.Instrumented.Example.go

-- The program go does not terminate.

go-loops = Lambda.Interpreter.Instrumented.Example.go-loops

-- The colists loop-sizes and go-sizes.

loop-sizes = Lambda.Interpreter.Instrumented.Example.loop-sizes
go-sizes   = Lambda.Interpreter.Instrumented.Example.go-sizes

-- The colist go-sizes matches the stack-sizes encountered when
-- interpreting go.

stack-sizes-go∼go-sizes =
  Lambda.Interpreter.Instrumented.Example.stack-sizes-go∼go-sizes

-- The least upper bound of go-sizes is 2.

lub-go-sizes-2 = Lambda.Interpreter.Instrumented.Example.lub-go-sizes-2

-- The program go runs in bounded stack space.

go-bounded-stack =
  Lambda.Interpreter.Instrumented.Example.go-bounded-stack
