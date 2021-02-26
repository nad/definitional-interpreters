------------------------------------------------------------------------
-- Virtual machine instructions, state etc.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Prelude

module Lambda.Virtual-machine.Instructions (Name : Type) where

open import Equality.Propositional

open import Lambda.Syntax Name

------------------------------------------------------------------------
-- Instruction set

mutual

  -- Instructions.

  data Instr (n : ℕ) : Type where
    var     : Fin n → Instr n
    clo     : Code (suc n) → Instr n
    app ret : Instr n
    cal tcl : Name → Instr n  -- Calls and tail calls.
    con     : Bool → Instr n
    bra     : Code n → Code n → Instr n

  -- Code.

  Code : ℕ → Type
  Code n = List (Instr n)

-- Environments and values.

open Closure Code

------------------------------------------------------------------------
-- Stacks and states

-- Stacks.

data Stack-element : Type where
  val : Value → Stack-element
  ret : ∀ {n} → Code n → Env n → Stack-element

Stack : Type
Stack = List Stack-element

-- States.

data State : Type where
  ⟨_,_,_⟩ : ∀ {n} → Code n → Stack → Env n → State

------------------------------------------------------------------------
-- Results

-- The result of running the VM one step.

data Result : Type where
  continue : State → Result
  done     : Value → Result
  crash    : Result
