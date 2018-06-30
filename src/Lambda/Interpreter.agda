------------------------------------------------------------------------
-- A definitional interpreter
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Interpreter where

import Equality.Propositional as E
open import Prelude

open import Maybe E.equality-with-J
open import Monad E.equality-with-J
open import Vec.Data E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity
open import Delay-monad.Monad

open import Lambda.Delay-crash
open import Lambda.Syntax

open Closure Tm

------------------------------------------------------------------------
-- The interpreter

infix 10 _∙_

mutual

  ⟦_⟧ : ∀ {i n} → Tm n → Env n → Delay-crash Value i
  ⟦ con i ⟧   ρ = return (con i)
  ⟦ var x ⟧   ρ = return (index x ρ)
  ⟦ ƛ t ⟧     ρ = return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧ ρ = ⟦ t₁ ⟧ ρ >>= λ v₁ →
                  ⟦ t₂ ⟧ ρ >>= λ v₂ →
                  v₁ ∙ v₂

  _∙_ : ∀ {i} → Value → Value → Delay-crash Value i
  con i  ∙ v₂ = fail
  ƛ t₁ ρ ∙ v₂ = laterDC (⟦ t₁ ⟧′ (v₂ ∷ ρ))

  ⟦_⟧′ : ∀ {i n} → Tm n → Env n → Delay-crash′ Value i
  force (run (⟦ t ⟧′ ρ)) = run (⟦ t ⟧ ρ)

------------------------------------------------------------------------
-- An example

-- The semantics of Ω is the non-terminating computation never.

Ω-loops : ∀ {i} → [ i ] run (⟦ Ω ⟧ []) ∼ never
Ω-loops =
  run (⟦ Ω ⟧ [])                                  ∼⟨⟩
  run (⟦ ω · ω ⟧ [])                              ∼⟨⟩
  run (ƛ ω-body [] ∙ ƛ ω-body [])                 ∼⟨⟩
  run (laterDC (⟦ ω-body ⟧′ (ƛ ω-body [] ∷ [])))  ∼⟨ later (λ { .force →

      run (⟦ ω-body ⟧ (ƛ ω-body [] ∷ []))              ∼⟨⟩
      run (ƛ ω-body [] ∙ ƛ ω-body [])                  ∼⟨⟩
      run (⟦ Ω ⟧ [])                                   ∼⟨ Ω-loops ⟩∼
      never                                            ∎ }) ⟩∼

  never                                           ∎
