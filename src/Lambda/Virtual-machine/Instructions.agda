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
    var : (x : Fin n) → Instr n
    clo : (c : Code (suc n)) → Instr n
    app : Instr n
    ret : Instr n
    cal : Name → Instr n
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

data StackElement : Set where
  val : (v : Value) → StackElement
  ret : ∀ {n} (c : Code n) (ρ : Env n) → StackElement

Stack : Set
Stack = List StackElement

-- States.

data State : Set where
  ⟨_,_,_⟩ : ∀ {n} (c : Code n) (s : Stack) (ρ : Env n) → State

pattern ⟨_∣_,_,_⟩ n c s ρ = ⟨_,_,_⟩ {n} c s ρ

-- The length of the stack.

stack-size : State → ℕ
stack-size ⟨ _ , s , _ ⟩ = length s

------------------------------------------------------------------------
-- Results

-- The result of running the VM one step.

data Result : Set where
  continue : (s : State) → Result
  done     : (v : Value) → Result
  crash    : Result
