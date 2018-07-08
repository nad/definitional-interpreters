------------------------------------------------------------------------
-- Virtual machine instructions, state etc.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Virtual-machine.Instructions (Name : Set) where

open import Equality.Propositional
open import Prelude

open import List equality-with-J using (length)

open import Lambda.Syntax Name

------------------------------------------------------------------------
-- Instruction set

mutual

  -- Instructions.

  data Instr (n : ℕ) : Set where
    var : Fin n → Instr n
    clo : Code (suc n) → Instr n
    app : Instr n
    ret : Instr n
    cal : Name → Instr n
    tcl : Name → Instr n  -- Tail call.
    con : Bool → Instr n
    bra : Code n → Code n → Instr n

  -- Code.

  Code : ℕ → Set
  Code n = List (Instr n)

-- Environments and values.

open Closure Code

------------------------------------------------------------------------
-- Stacks and states

-- Stacks.

data Stack-element : Set where
  val : Value → Stack-element
  ret : ∀ {n} → Code n → Env n → Stack-element

Stack : Set
Stack = List Stack-element

-- States.

data State : Set where
  ⟨_,_,_⟩ : ∀ {n} → Code n → Stack → Env n → State

-- The length of the stack.

stack-size : State → ℕ
stack-size ⟨ _ , s , _ ⟩ = length s

------------------------------------------------------------------------
-- Results

-- The result of running the VM one step.

data Result : Set where
  cont  : State → Result
  done  : Value → Result
  crash : Result
