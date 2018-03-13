------------------------------------------------------------------------
-- A compiler
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Compiler where

open import Equality.Propositional
open import Prelude

open import Vec.Data equality-with-J

open import Lambda.Syntax
open import Lambda.Virtual-machine

private
  module C = Closure Code
  module T = Closure Tm

-- The compiler (which takes a code continuation).

comp : ∀ {n} → Tm n → Code n → Code n
comp (con i)   c = con i ∷ c
comp (var x)   c = var x ∷ c
comp (ƛ t)     c = clo (comp t (ret ∷ [])) ∷ c
comp (t₁ · t₂) c = comp t₁ (comp t₂ (app ∷ c))

-- Environments and values can also be compiled.

mutual

  comp-env : ∀ {n} → T.Env n → C.Env n
  comp-env []      = []
  comp-env (v ∷ ρ) = comp-val v ∷ comp-env ρ

  comp-val : T.Value → C.Value
  comp-val (T.con i) = C.con i
  comp-val (T.ƛ t ρ) = C.ƛ (comp t (ret ∷ [])) (comp-env ρ)

-- Indexing commutes with compilation.

comp-index : ∀ {n} (x : Fin n) (ρ : T.Env n) →
             index x (comp-env ρ) ≡ comp-val (index x ρ)
comp-index ()       []
comp-index fzero    (v ∷ ρ) = refl
comp-index (fsuc i) (v ∷ ρ) = comp-index i ρ
