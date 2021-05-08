------------------------------------------------------------------------
-- A counterexample: The trace of stack sizes produced by the virtual
-- machine is not necessarily bisimilar to that produced by the
-- instrumented interpreter
------------------------------------------------------------------------

module Lambda.Interpreter.Stack-sizes.Counterexample where

open import Equality.Propositional as E using (_≡_)
open import Prelude
open import Prelude.Size

open import Colist E.equality-with-J
open import Function-universe E.equality-with-J
open import Vec.Data E.equality-with-J

import Lambda.Compiler
import Lambda.Interpreter.Stack-sizes
import Lambda.Virtual-machine
import Lambda.Virtual-machine.Instructions

-- This module uses a name type with two inhabitants.

open import Lambda.Syntax Bool

open Closure Tm

-- Two unary functions.

def : Bool → Tm 1
def true  = call false (con true)
def false = con true

-- The instrumented interpreter, compiler and virtual machine are
-- instantiated with this definition.

module I = Lambda.Interpreter.Stack-sizes def
open Lambda.Compiler def
open Lambda.Virtual-machine.Instructions Bool
open module VM = Lambda.Virtual-machine comp-name

-- A top-level term to get things going. The important property of
-- this term is that when it is compiled and the resulting code is
-- executed on the virtual machine, then one tail call is made to a
-- function that terminates successfully.

go : Tm 0
go = call true (con true)

-- The trace of stack sizes produced by the virtual machine is not
-- necessarily bisimilar to that produced by the instrumented
-- interpreter.

stack-sizes-not-bisimilar :
  ¬ [ ∞ ] VM.stack-sizes ⟨ comp₀ go , [] , [] ⟩ ∼ I.stack-sizes go
stack-sizes-not-bisimilar =
  [ ∞ ] VM.stack-sizes ⟨ comp₀ go , [] , [] ⟩ ∼ I.stack-sizes go  ↝⟨ take-cong 8 ⟩

  take 8 (VM.stack-sizes ⟨ comp₀ go , [] , [] ⟩) ≡
  take 8 (I.stack-sizes go)                                       ↔⟨⟩

  0 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷ 2 ∷ 1 ∷ [] ≡
  0 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷ 2 ∷ 2 ∷ 1 ∷ []                              ↝⟨ (λ ()) ⟩□

  ⊥                                                               □
