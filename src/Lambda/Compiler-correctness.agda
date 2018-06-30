------------------------------------------------------------------------
-- Compiler correctness
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Compiler-correctness where

import Equality.Propositional as E
open import Prelude
open import Tactic.By using (by)

open import Maybe E.equality-with-J
open import Monad E.equality-with-J using (return; _>>=_)
open import Vec.Data E.equality-with-J

open import Delay-monad.Bisimilarity
import Delay-monad.Monad

open import Lambda.Compiler
open import Lambda.Delay-crash
open import Lambda.Interpreter
open import Lambda.Syntax
open import Lambda.Virtual-machine

private
  module C = Closure Code
  module T = Closure Tm

------------------------------------------------------------------------
-- A lemma

-- A rearrangement lemma for ⟦_⟧.

⟦⟧-· :
  ∀ {n} (t₁ t₂ : Tm n) {ρ} {k : T.Value → Delay-crash C.Value ∞} →
  run (⟦ t₁ · t₂ ⟧ ρ >>= k) ∼
  run (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k)
⟦⟧-· t₁ t₂ {ρ} {k} =
  run (⟦ t₁ · t₂ ⟧ ρ >>= k)    ∼⟨⟩

  run ((do v₁ ← ⟦ t₁ ⟧ ρ
           v₂ ← ⟦ t₂ ⟧ ρ
           v₁ ∙ v₂) >>= k)     ∼⟨ symmetric (associativity (⟦ t₁ ⟧ _) _ _) ⟩

  run (do v₁ ← ⟦ t₁ ⟧ ρ
          (do v₂ ← ⟦ t₂ ⟧ ρ
              v₁ ∙ v₂) >>= k)  ∼⟨ (run (⟦ t₁ ⟧ _) ∎) >>=-cong (λ _ → symmetric (associativity (⟦ t₂ ⟧ _) _ _)) ⟩

  run (do v₁ ← ⟦ t₁ ⟧ ρ
          v₂ ← ⟦ t₂ ⟧ ρ
          v₁ ∙ v₂ >>= k)       ∎

------------------------------------------------------------------------
-- The semantics of the compiled program matches that of the source
-- code

-- Some lemmas.

mutual

  ⟦⟧-correct :
    ∀ {i n} t (ρ : T.Env n) {c s}
      {k : T.Value → Delay-crash C.Value ∞} →
    (∀ v → [ i ] run (exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩) ≈
                 run (k v)) →
    [ i ] run (exec ⟨ comp t c , s , comp-env ρ ⟩) ≈ run (⟦ t ⟧ ρ >>= k)

  ⟦⟧-correct (con i) ρ {c} {s} {k} hyp =
    run (exec ⟨ con i ∷ c , s , comp-env ρ ⟩)                     ≳⟨⟩
    run (exec ⟨ c , val (comp-val (T.con i)) ∷ s , comp-env ρ ⟩)  ≈⟨ hyp (T.con i) ⟩∼
    run (k (T.con i))                                             ∼⟨⟩
    run (⟦ con i ⟧ ρ >>= k)                                       ∎

  ⟦⟧-correct (var x) ρ {c} {s} {k} hyp =
    run (exec ⟨ var x ∷ c , s , comp-env ρ ⟩)                       ≳⟨⟩
    run (exec ⟨ c , val (index x (comp-env ρ)) ∷ s , comp-env ρ ⟩)  ≡⟨ by (comp-index x ρ) ⟩
    run (exec ⟨ c , val (comp-val (index x ρ)) ∷ s , comp-env ρ ⟩)  ≈⟨ hyp (index x ρ) ⟩∼
    run (k (index x ρ))                                             ∼⟨⟩
    run (⟦ var x ⟧ ρ >>= k)                                         ∎

  ⟦⟧-correct (ƛ t) ρ {c} {s} {k} hyp =
    run (exec ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩)   ≳⟨⟩
    run (exec ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩)  ≈⟨ hyp (T.ƛ t ρ) ⟩∼
    run (k (T.ƛ t ρ))                                             ∼⟨⟩
    run (⟦ ƛ t ⟧ ρ >>= k)                                         ∎

  ⟦⟧-correct (t₁ · t₂) ρ {c} {s} {k} hyp =
    run (exec ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩)  ≈⟨ (⟦⟧-correct t₁ _ λ v₁ → ⟦⟧-correct t₂ _ λ v₂ → ∙-correct v₁ v₂ hyp) ⟩∼
    run (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k)  ∼⟨ symmetric (⟦⟧-· t₁ t₂) ⟩
    run (⟦ t₁ · t₂ ⟧ ρ >>= k)                                    ∎

  ∙-correct :
    ∀ {i n} v₁ v₂ {ρ : T.Env n} {c s}
      {k : T.Value → Delay-crash C.Value ∞} →
    (∀ v → [ i ] run (exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩) ≈
                 run (k v)) →
    [ i ] run (exec ⟨ app ∷ c
                    , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
                    , comp-env ρ
                    ⟩) ≈
          run (v₁ ∙ v₂ >>= k)
  ∙-correct (T.con i) v₂ {ρ} {c} {s} {k} hyp =
    run (exec ⟨ app ∷ c
              , val (comp-val v₂) ∷ val (C.con i) ∷ s
              , comp-env ρ
              ⟩)                                       ≳⟨⟩

    run fail                                           ∼⟨⟩

    run (T.con i ∙ v₂ >>= k)                           ∎

  ∙-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} hyp =
    run (exec ⟨ app ∷ c
              , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
              , comp-env ρ
              ⟩)                                                    ≈⟨ later (λ { .force →

      run (exec ⟨ comp t₁ (ret ∷ [])
                , ret c (comp-env ρ) ∷ s
                , comp-val v₂ ∷ comp-env ρ₁
             ⟩)                                                          ∼⟨⟩

      run (exec ⟨ comp t₁ (ret ∷ [])
                , ret c (comp-env ρ) ∷ s
                , comp-env (v₂ ∷ ρ₁)
                ⟩)                                                       ≈⟨ ⟦⟧-correct t₁ (_ ∷ _) (λ v →

        run (exec ⟨ ret ∷ []
                  , val (comp-val v) ∷ ret c (comp-env ρ) ∷ s
                  , comp-env (v₂ ∷ ρ₁)
                  ⟩)                                                          ≳⟨⟩

        run (exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩)                  ≈⟨ hyp v ⟩∎

        run (k v)                                                             ∎) ⟩∼

      run (⟦ t₁ ⟧ (v₂ ∷ ρ₁) >>= k)                                       ∎ }) ⟩∎

    run (T.ƛ t₁ ρ₁ ∙ v₂ >>= k)                                      ∎

-- Compiler correctness. Note that the equality that is used here is
-- syntactic.

correct :
  ∀ t →
  run (exec ⟨ comp t [] , [] , [] ⟩) ≈
  run (⟦ t ⟧ [] >>= λ v → return (comp-val v))
correct t =
  run (exec ⟨ comp t [] , [] , [] ⟩)            ∼⟨⟩
  run (exec ⟨ comp t [] , [] , comp-env [] ⟩)   ≈⟨ ⟦⟧-correct t [] (λ v → laterˡ (return (just (comp-val v)) ∎)) ⟩
  run (⟦ t ⟧ [] >>= λ v → return (comp-val v))  ∎
