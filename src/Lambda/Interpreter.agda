------------------------------------------------------------------------
-- A definitional interpreter
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Prelude

import Lambda.Syntax

module Lambda.Interpreter
  {Name : Type}
  (open Lambda.Syntax Name)
  (def : Name → Tm 1)
  where

import Equality.Propositional as E

open import Monad E.equality-with-J
open import Vec.Data E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity

open import Lambda.Delay-crash

open Closure Tm

------------------------------------------------------------------------
-- The interpreter

infix 10 _∙_

mutual

  ⟦_⟧ : ∀ {i n} → Tm n → Env n → Delay-crash Value i
  ⟦ var x ⟧       ρ = return (index ρ x)
  ⟦ lam t ⟧       ρ = return (lam t ρ)
  ⟦ t₁ · t₂ ⟧     ρ = do v₁ ← ⟦ t₁ ⟧ ρ
                         v₂ ← ⟦ t₂ ⟧ ρ
                         v₁ ∙ v₂
  ⟦ call f t ⟧    ρ = do v ← ⟦ t ⟧ ρ
                         lam (def f) [] ∙ v
  ⟦ con b ⟧       ρ = return (con b)
  ⟦ if t₁ t₂ t₃ ⟧ ρ = do v₁ ← ⟦ t₁ ⟧ ρ
                         ⟦if⟧ v₁ t₂ t₃ ρ

  _∙_ : ∀ {i} → Value → Value → Delay-crash Value i
  lam t₁ ρ ∙ v₂ = later λ { .force → ⟦ t₁ ⟧ (v₂ ∷ ρ) }
  con _    ∙ _  = crash

  ⟦if⟧ : ∀ {i n} →
         Value → Tm n → Tm n → Env n → Delay-crash Value i
  ⟦if⟧ (lam _ _)   _  _  _ = crash
  ⟦if⟧ (con true)  t₂ t₃ ρ = ⟦ t₂ ⟧ ρ
  ⟦if⟧ (con false) t₂ t₃ ρ = ⟦ t₃ ⟧ ρ

------------------------------------------------------------------------
-- An example

-- The semantics of Ω is the non-terminating computation never.

Ω-loops : ∀ {i} → [ i ] ⟦ Ω ⟧ [] ∼ never
Ω-loops =
  ⟦ Ω ⟧ []                             ∼⟨⟩
  ⟦ ω · ω ⟧ []                         ∼⟨⟩
  lam ω-body [] ∙ lam ω-body []        ∼⟨ later (λ { .force →

      ⟦ ω-body ⟧ (lam ω-body [] ∷ [])       ∼⟨⟩
      lam ω-body [] ∙ lam ω-body []         ∼⟨⟩
      ⟦ Ω ⟧ []                              ∼⟨ Ω-loops ⟩∼
      never                                 ∎ }) ⟩∼

  never                                ∎

-- A more direct proof.

Ω-loops′ : ∀ {i} → [ i ] ⟦ Ω ⟧ [] ∼ never
Ω-loops′ = later λ { .force → Ω-loops′ }
