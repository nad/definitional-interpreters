------------------------------------------------------------------------
-- A virtual machine
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

import Lambda.Virtual-machine.Instructions

module Lambda.Virtual-machine
  {Name : Set}
  (open Lambda.Virtual-machine.Instructions Name)
  (def : Name → Code 1)
  where

open import Colist using (Colist)
open import Equality.Propositional
open import Prelude

open import List equality-with-J using (_++_)
open import Monad equality-with-J
open import Vec.Data equality-with-J

open import Lambda.Delay-crash
open import Lambda.Delay-crash-colist
open import Lambda.Syntax Name

open Closure (const Code)

-- A single step of the computation.

step : State → Result
step ⟨ var x     ∷ c ,                          s , ρ ⟩ = continue ⟨ c       , val (index x ρ)         ∷  s ,     ρ  ⟩
step ⟨ clo c′    ∷ c ,                          s , ρ ⟩ = continue ⟨ c       , val (ƛ {p = true} c′ ρ) ∷  s ,     ρ  ⟩
step ⟨ app       ∷ c , val v ∷ val (ƛ c′ ρ′) ∷  s , ρ ⟩ = continue ⟨ c′      , ret c ρ                 ∷  s , v ∷ ρ′ ⟩
step ⟨ ret       ∷ c , val v ∷     ret c′ ρ′ ∷  s , ρ ⟩ = continue ⟨ c′      , val v                   ∷  s ,     ρ′ ⟩
step ⟨ cal f     ∷ c ,                 val v ∷  s , ρ ⟩ = continue ⟨ def f   , ret c ρ                 ∷  s , v ∷ [] ⟩
step ⟨ tcl f     ∷ c , val v ∷     ret c′ ρ′ ∷  s , ρ ⟩ = continue ⟨ def f   , ret c′ ρ′               ∷  s , v ∷ [] ⟩
step ⟨ tcl f     ∷ c ,                 val v ∷ [] , ρ ⟩ = continue ⟨ def f   , ret c ρ                 ∷ [] , v ∷ [] ⟩
step ⟨ con b     ∷ c ,                          s , ρ ⟩ = continue ⟨ c       , val (con b)             ∷  s ,     ρ  ⟩
step ⟨ bra c₁ c₂ ∷ c ,       val (con true)  ∷  s , ρ ⟩ = continue ⟨ c₁ ++ c ,                            s ,     ρ  ⟩
step ⟨ bra c₁ c₂ ∷ c ,       val (con false) ∷  s , ρ ⟩ = continue ⟨ c₂ ++ c ,                            s ,     ρ  ⟩
step ⟨ zero ∣ []     ,                 val v ∷ [] , ρ ⟩ = done v
step _                                                  = crash

-- A functional semantics for the VM. The result includes a trace of
-- all the encountered states.

mutual

  exec⁺ : ∀ {i} → State → Delay-crash-colist State Value i
  exec⁺ s = later s λ { .force → exec⁺′ (step s) }

  exec⁺′ : ∀ {i} → Result → Delay-crash-colist State Value i
  exec⁺′ (continue s) = exec⁺ s
  exec⁺′ (done v)     = return v
  exec⁺′ crash        = crash

-- The semantics without the trace of states.

exec : ∀ {i} → State → Delay-crash Value i
exec = delay-crash ∘ exec⁺

-- The stack sizes of all the encountered states.

stack-sizes : ∀ {i} → State → Colist ℕ i
stack-sizes = Colist.map stack-size ∘ colist ∘ exec⁺
