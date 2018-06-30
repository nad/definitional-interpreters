------------------------------------------------------------------------
-- Compiler correctness
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

import Lambda.Syntax

module Lambda.Compiler-correctness
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm 1)
  where

import Equality.Propositional as E
open import Prelude
import Tactic.By as By

open import List E.equality-with-J using (_++_)
open import Maybe E.equality-with-J
open import Monad E.equality-with-J using (return; _>>=_)
open import Vec.Data E.equality-with-J

open import Delay-monad.Bisimilarity
import Delay-monad.Monad

open import Lambda.Compiler def
open import Lambda.Delay-crash
open import Lambda.Interpreter def
open import Lambda.Virtual-machine.Instructions Name
open import Lambda.Virtual-machine comp-name

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

  ⟦⟧-correct (var x) ρ {c} {s} {k} hyp =
    run (exec ⟨ var x ∷ c , s , comp-env ρ ⟩)                            ≳⟨⟩
    run (exec ⟨ c , val By.⟨ index x (comp-env ρ) ⟩ ∷ s , comp-env ρ ⟩)  ≡⟨ By.⟨by⟩ (comp-index x ρ) ⟩
    run (exec ⟨ c , val (comp-val (index x ρ)) ∷ s , comp-env ρ ⟩)       ≈⟨ hyp (index x ρ) ⟩∼
    run (k (index x ρ))                                                  ∼⟨⟩
    run (⟦ var x ⟧ ρ >>= k)                                              ∎

  ⟦⟧-correct (ƛ t) ρ {c} {s} {k} hyp =
    run (exec ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩)   ≳⟨⟩
    run (exec ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩)  ≈⟨ hyp (T.ƛ t ρ) ⟩∼
    run (k (T.ƛ t ρ))                                             ∼⟨⟩
    run (⟦ ƛ t ⟧ ρ >>= k)                                         ∎

  ⟦⟧-correct (t₁ · t₂) ρ {c} {s} {k} hyp =
    run (exec ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩)  ≈⟨ (⟦⟧-correct t₁ _ λ v₁ → ⟦⟧-correct t₂ _ λ v₂ → ∙-correct v₁ v₂ hyp) ⟩∼
    run (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k)  ∼⟨ symmetric (⟦⟧-· t₁ t₂) ⟩
    run (⟦ t₁ · t₂ ⟧ ρ >>= k)                                    ∎

  ⟦⟧-correct (call f t) ρ {c} {s} {k} hyp =
    run (exec ⟨ comp (call f t) c , s , comp-env ρ ⟩)                     ∼⟨⟩

    run (exec ⟨ comp t (cal f ∷ c) , s , comp-env ρ ⟩)                    ≈⟨ (⟦⟧-correct t _ λ v →

      run (exec ⟨ cal f ∷ c , val (comp-val v) ∷ s , comp-env ρ ⟩)              ≈⟨ (later λ { .force →

        run (exec ⟨ comp (def f) (ret ∷ [])
                  , ret c (comp-env ρ) ∷ s
                  , comp-val v ∷ []
                  ⟩)                                                                  ∼⟨⟩

        run (exec ⟨ comp (def f) (ret ∷ [])
                  , ret c (comp-env ρ) ∷ s
                  , comp-env (v ∷ [])
                  ⟩)                                                                  ≈⟨ (⟦⟧-correct (def f) (v ∷ []) λ v′ →

          run (exec ⟨ ret ∷ []
                    , val (comp-val v′) ∷ ret c (comp-env ρ) ∷ s
                    , comp-env (v ∷ [])
                    ⟩)                                                                      ≳⟨⟩

          run (exec ⟨ c
                    , val (comp-val v′) ∷ s
                    , comp-env ρ
                    ⟩)                                                                      ≈⟨ hyp v′ ⟩∼

          run (k v′)                                                                        ∎) ⟩∼

        run (⟦ def f ⟧ (v ∷ []) >>= k)                                                ∎ }) ⟩∼

      run (T.ƛ (def f) [] ∙ v >>= k)                                            ∎) ⟩∼

    run (⟦ t ⟧ ρ >>= λ v → T.ƛ (def f) [] ∙ v >>= k)                      ∼⟨ associativity (⟦ t ⟧ ρ) _ _ ⟩

    run ((⟦ t ⟧ ρ >>= λ v → T.ƛ (def f) [] ∙ v) >>= k)                    ∼⟨⟩

    run (⟦ call f t ⟧ ρ >>= k)                                            ∎

  ⟦⟧-correct (con b) ρ {c} {s} {k} hyp =
    run (exec ⟨ con b ∷ c , s , comp-env ρ ⟩)                     ≳⟨⟩
    run (exec ⟨ c , val (comp-val (T.con b)) ∷ s , comp-env ρ ⟩)  ≈⟨ hyp (T.con b) ⟩∼
    run (k (T.con b))                                             ∼⟨⟩
    run (⟦ con b ⟧ ρ >>= k)                                       ∎

  ⟦⟧-correct (if t₁ t₂ t₃) ρ {c} {s} {k} hyp =
    run (exec ⟨ comp t₁ (bra (comp t₂ []) (comp t₃ []) ∷ c)
              , s
              , comp-env ρ
              ⟩)                                             ≈⟨ (⟦⟧-correct t₁ _ λ v₁ → ⟦if⟧-correct v₁ t₂ t₃ hyp) ⟩∼

    run (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦if⟧ v₁ t₂ t₃ ρ >>= k)          ∼⟨ associativity (⟦ t₁ ⟧ ρ) _ _ ⟩

    run ((⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦if⟧ v₁ t₂ t₃ ρ) >>= k)        ∼⟨⟩

    run (⟦ if t₁ t₂ t₃ ⟧ ρ >>= k)                            ∎

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

  ∙-correct (T.con b) v₂ {ρ} {c} {s} {k} hyp =
    run (exec ⟨ app ∷ c
              , val (comp-val v₂) ∷ val (comp-val (T.con b)) ∷ s
              , comp-env ρ
              ⟩)                                                  ≳⟨⟩

    run fail                                                      ∼⟨⟩

    run (T.con b ∙ v₂ >>= k)                                      ∎

  ⟦if⟧-correct :
    ∀ {i n} v₁ t₂ t₃ {ρ : T.Env n} {c s}
      {k : T.Value → Delay-crash C.Value ∞} →
    (∀ v → [ i ] run (exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩) ≈
                 run (k v)) →
    [ i ] run (exec ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
                    , val (comp-val v₁) ∷ s
                    , comp-env ρ
                    ⟩) ≈
          run (⟦if⟧ v₁ t₂ t₃ ρ >>= k)

  ⟦if⟧-correct (T.ƛ t₁ ρ₁) t₂ t₃ {ρ} {c} {s} {k} hyp =
    run (exec ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
              , val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
              , comp-env ρ
              ⟩)                                   ≳⟨⟩

    run fail                                       ∼⟨⟩

    run (⟦if⟧ (T.ƛ t₁ ρ₁) t₂ t₃ ρ >>= k)           ∎

  ⟦if⟧-correct (T.con true) t₂ t₃ {ρ} {c} {s} {k} hyp =
    run (exec ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
              , val (comp-val (T.con true)) ∷ s
              , comp-env ρ
              ⟩)                                     ≳⟨⟩

    run (exec ⟨ comp t₂ [] ++ c , s , comp-env ρ ⟩)  ≡⟨ By.by (comp-++ t₂) ⟩

    run (exec ⟨ comp t₂ c , s , comp-env ρ ⟩)        ≈⟨ ⟦⟧-correct t₂ _ hyp ⟩∼

    run (⟦ t₂ ⟧ ρ >>= k)                             ∼⟨⟩

    run (⟦if⟧ (T.con true) t₂ t₃ ρ >>= k)            ∎

  ⟦if⟧-correct (T.con false) t₂ t₃ {ρ} {c} {s} {k} hyp =
    run (exec ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
              , val (comp-val (T.con false)) ∷ s
              , comp-env ρ
              ⟩)                                     ≳⟨⟩

    run (exec ⟨ comp t₃ [] ++ c , s , comp-env ρ ⟩)  ≡⟨ By.by (comp-++ t₃) ⟩

    run (exec ⟨ comp t₃ c , s , comp-env ρ ⟩)        ≈⟨ ⟦⟧-correct t₃ _ hyp ⟩∼

    run (⟦ t₃ ⟧ ρ >>= k)                             ∼⟨⟩

    run (⟦if⟧ (T.con false) t₂ t₃ ρ >>= k)           ∎

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
