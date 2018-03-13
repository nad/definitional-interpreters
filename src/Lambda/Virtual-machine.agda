------------------------------------------------------------------------
-- A virtual machine
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Virtual-machine where

open import Equality.Propositional
open import Prelude

open import Maybe equality-with-J
open import Monad equality-with-J
open import Vec.Data equality-with-J

open import Delay-monad
open import Delay-monad.Monad

open import Lambda.Interpreter
open import Lambda.Syntax

------------------------------------------------------------------------
-- Instruction set

mutual

  -- Instructions.

  data Instr (n : ℕ) : Set where
    var : (x : Fin n) → Instr n
    con : (i : ℕ) → Instr n
    clo : (c : Code (suc n)) → Instr n
    app : Instr n
    ret : Instr n

  -- Code.

  Code : ℕ → Set
  Code n = List (Instr n)

-- Environments and values.

open Closure Code

------------------------------------------------------------------------
-- Stacks and states

-- Stacks.

data StackElement : Set where
  val : (v : Value) → StackElement
  ret : ∀ {n} (c : Code n) (ρ : Env n) → StackElement

Stack : Set
Stack = List StackElement

-- States.

data State : Set where
  ⟨_,_,_⟩ : ∀ {n} (c : Code n) (s : Stack) (ρ : Env n) → State

pattern ⟨_∣_,_,_⟩ n c s ρ = ⟨_,_,_⟩ {n} c s ρ

------------------------------------------------------------------------
-- A kind of small-step semantics for the virtual machine

-- The result of running the VM one step.

data Result : Set where
  continue : (s : State) → Result
  done     : (v : Value) → Result
  crash    : Result

-- A single step of the computation.

step : State → Result
step ⟨ var x  ∷ c ,                          s , ρ ⟩ = continue ⟨ c  , val (index x ρ) ∷ s ,     ρ  ⟩
step ⟨ con i  ∷ c ,                          s , ρ ⟩ = continue ⟨ c  , val (con i)     ∷ s ,     ρ  ⟩
step ⟨ clo c′ ∷ c ,                          s , ρ ⟩ = continue ⟨ c  , val (ƛ c′ ρ)    ∷ s ,     ρ  ⟩
step ⟨ app    ∷ c , val v ∷ val (ƛ c′ ρ′) ∷  s , ρ ⟩ = continue ⟨ c′ , ret c ρ         ∷ s , v ∷ ρ′ ⟩
step ⟨ ret    ∷ c , val v ∷ ret c′ ρ′     ∷  s , ρ ⟩ = continue ⟨ c′ , val v           ∷ s ,     ρ′ ⟩
step ⟨ zero ∣ []  ,                 val v ∷ [] , ρ ⟩ = done v
step _                                               = crash

mutual

  -- A functional semantics for the VM.

  exec : ∀ {i} → State → M i Value
  exec s with step s
  ... | continue s′ = laterM (exec′ s′)
  ... | done v      = return v
  ... | crash       = fail

  exec′ : ∀ {i} → State → M′ i Value
  force (run (exec′ s)) = run (exec s)
