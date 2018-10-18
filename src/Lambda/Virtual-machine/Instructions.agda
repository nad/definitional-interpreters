------------------------------------------------------------------------
-- Virtual machine instructions, state etc.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Virtual-machine.Instructions (Name : Set) where

open import Equality.Propositional
open import Prelude

open import Lambda.Syntax Name

------------------------------------------------------------------------
-- Instruction set

mutual

  -- Instructions.

  data Instr (n : ℕ) : Set where
    var     : Fin n → Instr n
    clo     : Code (suc n) → Instr n
    app ret : Instr n
    cal tcl : Name → Instr n  -- Calls and tail calls.
    con     : Bool → Instr n
    bra     : Code n → Code n → Instr n

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

------------------------------------------------------------------------
-- Results

-- The result of running the VM one step.

data Result : Set where
  continue : State → Result
  done     : Value → Result
  crash    : Result
