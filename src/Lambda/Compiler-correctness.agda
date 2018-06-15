------------------------------------------------------------------------
-- Compiler correctness
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Compiler-correctness where

import Equality.Propositional as E
open import Prelude
open import Tactic.By using (by)

open import Maybe E.equality-with-J hiding (_>>=′_)
open import Monad E.equality-with-J
open import Vec.Data E.equality-with-J

open import Delay-monad.Bisimilarity
open import Delay-monad.Monad

open import Lambda.Compiler
open import Lambda.Interpreter
open import Lambda.Virtual-machine
open import Lambda.Syntax
open import Lambda.Virtual-machine

private
  module C = Closure Code
  module T = Closure Tm

-- Bind preserves strong bisimilarity.

infixl 5 _>>=-congM_

_>>=-congM_ :
  ∀ {i ℓ} {A B : Set ℓ} {x y : M ∞ A} {f g : A → M ∞ B} →
  [ i ] run x ∼ run y →
  (∀ z → [ i ] run (f z) ∼ run (g z)) →
  [ i ] run (x >>= f) ∼ run (y >>= g)
p >>=-congM q = p >>=-cong [ (λ _ → run fail ∎) , q ]

-- Bind is associative.

associativityM :
  ∀ {ℓ} {A B C : Set ℓ} (x : M ∞ A) (f : A → M ∞ B) (g : B → M ∞ C) →
  run (x >>= (λ x → f x >>= g)) ∼ run (x >>= f >>= g)
associativityM x f g =
  run (x >>= λ x → f x >>= g)                                       ∼⟨⟩

  run x >>=′ maybe (λ x → run (f x >>= g)) (return nothing)         ∼⟨ (run x ∎) >>=-cong [ (λ _ → run fail ∎) , (λ x → run (f x >>= g) ∎) ] ⟩

  run x >>=′ (λ x → maybe (MaybeT.run ∘ f) (return nothing) x >>=′
                    maybe (MaybeT.run ∘ g) (return nothing))        ∼⟨ associativity′ (run x) _ _ ⟩

  run x >>=′ maybe (MaybeT.run ∘ f) (return nothing)
        >>=′ maybe (MaybeT.run ∘ g) (return nothing)                ∼⟨⟩

  run (x >>= f >>= g)                                               ∎

-- Compiler correctness.

mutual

  ⟦⟧-correct :
    ∀ {i n} t (ρ : T.Env n) {c s} {k : T.Value → M ∞ C.Value} →
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
    run (exec ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩)    ≈⟨ (⟦⟧-correct t₁ _ λ v₁ → ⟦⟧-correct t₂ _ λ v₂ → ∙-correct v₁ v₂ hyp) ⟩∼

    run (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k)    ∼⟨ (run (⟦ t₁ ⟧ ρ) ∎) >>=-congM (λ _ → associativityM (⟦ t₂ ⟧ ρ) _ _) ⟩

    run (⟦ t₁ ⟧ ρ >>= λ v₁ → (⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂) >>= k)  ∼⟨ associativityM (⟦ t₁ ⟧ ρ) _ _ ⟩

    run (⟦ t₁ · t₂ ⟧ ρ >>= k)                                      ∎

  ∙-correct :
    ∀ {i n} v₁ v₂ {ρ : T.Env n} {c s} {k : T.Value → M ∞ C.Value} →
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
              ⟩)                                       ∼⟨⟩

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

-- Note that the equality that is used here is syntactic.

correct :
  ∀ t →
  exec ⟨ comp t [] , [] , [] ⟩ ≈M
  ⟦ t ⟧ [] >>= λ v → return (comp-val v)
correct t =
  run (exec ⟨ comp t [] , [] , [] ⟩)            ∼⟨⟩
  run (exec ⟨ comp t [] , [] , comp-env [] ⟩)   ≈⟨ ⟦⟧-correct t [] (λ v → return (just (comp-val v)) ∎) ⟩
  run (⟦ t ⟧ [] >>= λ v → return (comp-val v))  ∎