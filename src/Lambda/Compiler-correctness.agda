------------------------------------------------------------------------
-- Compiler correctness
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Prelude

import Lambda.Syntax

module Lambda.Compiler-correctness
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm true 1)
  where

import Equality.Propositional as E
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
  module C = Closure (const Code)
  module T = Closure Tm

------------------------------------------------------------------------
-- A lemma

-- A rearrangement lemma for ⟦_⟧.

⟦⟧-· :
  ∀ p {n} (t₁ t₂ : Tm false n) {ρ}
      {k : T.Value → Delay-crash C.Value ∞} →
  run (⟦ _·_ {p = p} t₁ t₂ ⟧ ρ >>= k) ∼
  run (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k)
⟦⟧-· p t₁ t₂ {ρ} {k} =
  run (⟦ _·_ {p = p} t₁ t₂ ⟧ ρ >>= k)  ∼⟨⟩

  run ((do v₁ ← ⟦ t₁ ⟧ ρ
           v₂ ← ⟦ t₂ ⟧ ρ
           v₁ ∙ v₂) >>= k)             ∼⟨ symmetric (associativity (⟦ t₁ ⟧ _) _ _) ⟩

  run (do v₁ ← ⟦ t₁ ⟧ ρ
          (do v₂ ← ⟦ t₂ ⟧ ρ
              v₁ ∙ v₂) >>= k)          ∼⟨ (run (⟦ t₁ ⟧ _) ∎) >>=-cong (λ _ → symmetric (associativity (⟦ t₂ ⟧ _) _ _)) ⟩

  run (do v₁ ← ⟦ t₁ ⟧ ρ
          v₂ ← ⟦ t₂ ⟧ ρ
          v₁ ∙ v₂ >>= k)               ∎

------------------------------------------------------------------------
-- Well-formed continuations and stacks

-- A continuation is OK with respect to a certain state if the
-- following property is satisfied.

Cont-OK : Size → State → (T.Value → Delay-crash C.Value ∞) → Set
Cont-OK i ⟨ c , s , ρ ⟩ k =
  ∀ v → [ i ] run (exec ⟨ c , val (comp-val v) ∷ s , ρ ⟩) ≈
              run (k v)

-- If the In-tail-context parameter indicates that we are in a tail
-- context and the stack is non-empty, then the stack must be related
-- to the continuation in a certain way.

data Stack-OK (i : Size) (k : T.Value → Delay-crash C.Value ∞) :
              In-tail-context → Stack → Set where
  unrestricted  : ∀ {s} → Stack-OK i k false s
  restricted-[] : Stack-OK i k true []
  restricted-∷  : ∀ {s n c} {ρ : C.Env n} →
                  Cont-OK i ⟨ c , s , ρ ⟩ k →
                  Stack-OK i k true (ret c ρ ∷ s)

-- The empty stack is always OK.

[]-ok : ∀ {p i k} → Stack-OK i k p []
[]-ok {true}  = restricted-[]
[]-ok {false} = unrestricted

-- Non-empty stacks satisfying a certain property are always OK.

ret-ok :
  ∀ {p i s n c} {ρ : C.Env n} {k} →
  Cont-OK i ⟨ c , s , ρ ⟩ k →
  Stack-OK i k p (ret c ρ ∷ s)
ret-ok {true}  c-ok = restricted-∷ c-ok
ret-ok {false} _    = unrestricted

------------------------------------------------------------------------
-- The semantics of the compiled program matches that of the source
-- code

mutual

  -- Some lemmas making up the main part of the compiler correctness
  -- result.

  ⟦⟧-correct :
    ∀ {p i n} (t : Tm p n) (ρ : T.Env n) {c s}
      {k : T.Value → Delay-crash C.Value ∞} →
    Stack-OK i k p s →
    Cont-OK i ⟨ c , s , comp-env ρ ⟩ k →
    [ i ] run (exec ⟨ comp t c , s , comp-env ρ ⟩) ≈
          run (⟦ t ⟧ ρ >>= k)

  ⟦⟧-correct {p} (var x) ρ {c} {s} {k} _ c-ok =
    run (exec ⟨ var x ∷ c , s , comp-env ρ ⟩)                            ≳⟨⟩
    run (exec ⟨ c , val By.⟨ index x (comp-env ρ) ⟩ ∷ s , comp-env ρ ⟩)  ≡⟨ By.⟨by⟩ (comp-index x ρ) ⟩
    run (exec ⟨ c , val (comp-val (index x ρ)) ∷ s , comp-env ρ ⟩)       ≈⟨ c-ok (index x ρ) ⟩∼
    run (k (index x ρ))                                                  ∼⟨⟩
    run (⟦ var {p = p} x ⟧ ρ >>= k)                                      ∎

  ⟦⟧-correct {p} (ƛ t) ρ {c} {s} {k} _ c-ok =
    run (exec ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩)   ≳⟨⟩
    run (exec ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩)  ≈⟨ c-ok (T.ƛ t ρ) ⟩∼
    run (k (T.ƛ t ρ))                                             ∼⟨⟩
    run (⟦ ƛ {p = p} t ⟧ ρ >>= k)                                 ∎

  ⟦⟧-correct {p} (t₁ · t₂) ρ {c} {s} {k} _ c-ok =
    run (exec ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩)  ≈⟨ (⟦⟧-correct t₁ _ unrestricted λ v₁ →

      run (exec ⟨ comp t₂ (app ∷ c)
                , val (comp-val v₁) ∷ s
                , comp-env ρ
                ⟩)                                                     ≈⟨ (⟦⟧-correct t₂ _ unrestricted λ v₂ →

        run (exec ⟨ app ∷ c
                  , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
                  , comp-env ρ
                  ⟩)                                                         ≈⟨ ∙-correct v₁ v₂ c-ok ⟩∼

        run (v₁ ∙ v₂ >>= k)                                                  ∎) ⟩∼

      run (⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k)                          ∎) ⟩∼

    run (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k)  ∼⟨ symmetric (⟦⟧-· p t₁ t₂) ⟩

    run (⟦ _·_ {p = p} t₁ t₂ ⟧ ρ >>= k)                          ∎

  ⟦⟧-correct (call f t) ρ {c} {s} {k} unrestricted c-ok =
    run (exec ⟨ comp (call {p = false} f t) c , s , comp-env ρ ⟩)   ∼⟨⟩

    run (exec ⟨ comp t (cal f ∷ c) , s , comp-env ρ ⟩)              ≈⟨ (⟦⟧-correct t _ unrestricted λ v →

      run (exec ⟨ cal f ∷ c , val (comp-val v) ∷ s , comp-env ρ ⟩)        ≈⟨ (later λ { .force →

        run (exec ⟨ comp-name f
                  , ret c (comp-env ρ) ∷ s
                  , comp-val v ∷ []
                  ⟩)                                                            ≈⟨ ret-lemma (def f) [] c-ok ⟩∼

        run (⟦ def f ⟧ (v ∷ []) >>= k)                                          ∎ }) ⟩∼

      run (T.ƛ (def f) [] ∙ v >>= k)                                      ∎) ⟩∼

    run (⟦ t ⟧ ρ >>= λ v → T.ƛ (def f) [] ∙ v >>= k)                ∼⟨ associativity (⟦ t ⟧ ρ) _ _ ⟩

    run ((⟦ t ⟧ ρ >>= λ v → T.ƛ (def f) [] ∙ v) >>= k)              ∼⟨⟩

    run (⟦ call {p = false} f t ⟧ ρ >>= k)                          ∎

  ⟦⟧-correct (call f t) ρ {c} {[]} {k} restricted-[] c-ok =
    run (exec ⟨ comp (call {p = true} f t) c , [] , comp-env ρ ⟩)    ∼⟨⟩

    run (exec ⟨ comp t (tcl f ∷ c) , [] , comp-env ρ ⟩)              ≈⟨ (⟦⟧-correct t _ unrestricted λ v →

      run (exec ⟨ tcl f ∷ c , val (comp-val v) ∷ [] , comp-env ρ ⟩)        ≈⟨ (later λ { .force →

        run (exec ⟨ comp-name f
                  , ret c (comp-env ρ) ∷ []
                  , comp-val v ∷ []
                  ⟩)                                                             ≈⟨ ret-lemma (def f) [] c-ok ⟩∼

        run (⟦ def f ⟧ (v ∷ []) >>= k)                                           ∎ }) ⟩∼

      run (T.ƛ (def f) [] ∙ v >>= k)                                       ∎) ⟩∼

    run (⟦ t ⟧ ρ >>= λ v → T.ƛ (def f) [] ∙ v >>= k)                 ∼⟨ associativity (⟦ t ⟧ ρ) _ _ ⟩

    run ((⟦ t ⟧ ρ >>= λ v → T.ƛ (def f) [] ∙ v) >>= k)               ∼⟨⟩

    run (⟦ call {p = true} f t ⟧ ρ >>= k)                            ∎

  ⟦⟧-correct (call f t) ρ {c} {ret c′ ρ′ ∷ s} {k}
             (restricted-∷ c-ok) _ =
    run (exec ⟨ comp (call {p = true} f t) c
              , ret c′ ρ′ ∷ s
              , comp-env ρ
              ⟩)                                                    ∼⟨⟩

    run (exec ⟨ comp t (tcl f ∷ c) , ret c′ ρ′ ∷ s , comp-env ρ ⟩)  ≈⟨ (⟦⟧-correct t _ unrestricted λ v →

      run (exec ⟨ tcl f ∷ c
                , val (comp-val v) ∷ ret c′ ρ′ ∷ s
                , comp-env ρ
                ⟩)                                                        ≈⟨ (later λ { .force →

        run (exec ⟨ comp-name f
                  , ret c′ ρ′ ∷ s
                  , comp-val v ∷ []
                  ⟩)                                                            ≈⟨ ret-lemma (def f) [] c-ok ⟩∼

        run (⟦ def f ⟧ (v ∷ []) >>= k)                                          ∎ }) ⟩∼

      run (T.ƛ (def f) [] ∙ v >>= k)                                      ∎) ⟩∼

    run (⟦ t ⟧ ρ >>= λ v → T.ƛ (def f) [] ∙ v >>= k)                ∼⟨ associativity (⟦ t ⟧ ρ) _ _ ⟩

    run ((⟦ t ⟧ ρ >>= λ v → T.ƛ (def f) [] ∙ v) >>= k)              ∼⟨⟩

    run (⟦ call {p = true} f t ⟧ ρ >>= k)                           ∎

  ⟦⟧-correct {p} (con b) ρ {c} {s} {k} _ c-ok =
    run (exec ⟨ con b ∷ c , s , comp-env ρ ⟩)                     ≳⟨⟩
    run (exec ⟨ c , val (comp-val (T.con b)) ∷ s , comp-env ρ ⟩)  ≈⟨ c-ok (T.con b) ⟩∼
    run (k (T.con b))                                             ∼⟨⟩
    run (⟦ con {p = p} b ⟧ ρ >>= k)                               ∎

  ⟦⟧-correct (if t₁ t₂ t₃) ρ {c} {s} {k} s-ok c-ok =
    run (exec ⟨ comp t₁ (bra (comp t₂ []) (comp t₃ []) ∷ c)
              , s
              , comp-env ρ
              ⟩)                                             ≈⟨ (⟦⟧-correct t₁ _ unrestricted λ v₁ → ⟦if⟧-correct v₁ t₂ t₃ s-ok c-ok) ⟩∼

    run (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦if⟧ v₁ t₂ t₃ ρ >>= k)          ∼⟨ associativity (⟦ t₁ ⟧ ρ) _ _ ⟩

    run ((⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦if⟧ v₁ t₂ t₃ ρ) >>= k)        ∼⟨⟩

    run (⟦ if t₁ t₂ t₃ ⟧ ρ >>= k)                            ∎

  ret-lemma :
    ∀ {p i n n′} (t : Tm p (1 + n)) ρ {ρ′ : C.Env n′} {c s v}
      {k : T.Value → Delay-crash C.Value ∞} →
    Cont-OK i ⟨ c , s , ρ′ ⟩ k →
    [ i ] run (exec ⟨ comp t (ret ∷ [])
                    , ret c ρ′ ∷ s
                    , comp-val v ∷ comp-env ρ
                    ⟩) ≈
          run (⟦ t ⟧ (v ∷ ρ) >>= k)
  ret-lemma t ρ {ρ′} {c} {s} {v} {k} c-ok =
    run (exec ⟨ comp t (ret ∷ [])
              , ret c ρ′ ∷ s
              , comp-val v ∷ comp-env ρ
              ⟩)                                     ∼⟨⟩

    run (exec ⟨ comp t (ret ∷ [])
              , ret c ρ′ ∷ s
              , comp-env (v ∷ ρ)
              ⟩)                                     ≈⟨ (⟦⟧-correct t (_ ∷ _) (ret-ok c-ok) λ v′ →

      run (exec ⟨ ret ∷ []
                , val (comp-val v′) ∷ ret c ρ′ ∷ s
                , comp-env (v ∷ ρ)
                ⟩)                                         ≳⟨⟩

      run (exec ⟨ c , val (comp-val v′) ∷ s , ρ′ ⟩)        ≈⟨ c-ok v′ ⟩∼

      run (k v′)                                           ∎) ⟩∼

    run (⟦ t ⟧ (v ∷ ρ) >>= k)                        ∎

  ∙-correct :
    ∀ {i n} v₁ v₂ {ρ : C.Env n} {c s}
      {k : T.Value → Delay-crash C.Value ∞} →
    Cont-OK i ⟨ c , s , ρ ⟩ k →
    [ i ] run (exec ⟨ app ∷ c
                    , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
                    , ρ
                    ⟩) ≈
          run (v₁ ∙ v₂ >>= k)

  ∙-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} c-ok =
    run (exec ⟨ app ∷ c
              , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
              , ρ
              ⟩)                                                    ≈⟨ later (λ { .force →

      run (exec ⟨ comp t₁ (ret ∷ [])
                , ret c ρ ∷ s
                , comp-val v₂ ∷ comp-env ρ₁
             ⟩)                                                          ≈⟨ ret-lemma t₁ _ c-ok ⟩∼

      run (⟦ t₁ ⟧ (v₂ ∷ ρ₁) >>= k)                                       ∎ }) ⟩∎

    run (T.ƛ t₁ ρ₁ ∙ v₂ >>= k)                                      ∎

  ∙-correct (T.con b) v₂ {ρ} {c} {s} {k} _ =
    run (exec ⟨ app ∷ c
              , val (comp-val v₂) ∷ val (comp-val (T.con b)) ∷ s
              , ρ
              ⟩)                                                  ≳⟨⟩

    run fail                                                      ∼⟨⟩

    run (T.con b ∙ v₂ >>= k)                                      ∎

  ⟦if⟧-correct :
    ∀ {i p n} v₁ (t₂ t₃ : Tm p n) {ρ : T.Env n} {c s}
      {k : T.Value → Delay-crash C.Value ∞} →
    Stack-OK i k p s →
    Cont-OK i ⟨ c , s , comp-env ρ ⟩ k →
    [ i ] run (exec ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
                    , val (comp-val v₁) ∷ s
                    , comp-env ρ
                    ⟩) ≈
          run (⟦if⟧ v₁ t₂ t₃ ρ >>= k)

  ⟦if⟧-correct (T.ƛ t₁ ρ₁) t₂ t₃ {ρ} {c} {s} {k} _ _ =
    run (exec ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
              , val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
              , comp-env ρ
              ⟩)                                   ≳⟨⟩

    run fail                                       ∼⟨⟩

    run (⟦if⟧ (T.ƛ t₁ ρ₁) t₂ t₃ ρ >>= k)           ∎

  ⟦if⟧-correct (T.con true) t₂ t₃ {ρ} {c} {s} {k} s-ok c-ok =
    run (exec ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
              , val (comp-val (T.con true)) ∷ s
              , comp-env ρ
              ⟩)                                     ≳⟨⟩

    run (exec ⟨ comp t₂ [] ++ c , s , comp-env ρ ⟩)  ≡⟨ By.by (comp-++ t₂) ⟩

    run (exec ⟨ comp t₂ c , s , comp-env ρ ⟩)        ≈⟨ ⟦⟧-correct t₂ _ s-ok c-ok ⟩∼

    run (⟦ t₂ ⟧ ρ >>= k)                             ∼⟨⟩

    run (⟦if⟧ (T.con true) t₂ t₃ ρ >>= k)            ∎

  ⟦if⟧-correct (T.con false) t₂ t₃ {ρ} {c} {s} {k} s-ok c-ok =
    run (exec ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
              , val (comp-val (T.con false)) ∷ s
              , comp-env ρ
              ⟩)                                     ≳⟨⟩

    run (exec ⟨ comp t₃ [] ++ c , s , comp-env ρ ⟩)  ≡⟨ By.by (comp-++ t₃) ⟩

    run (exec ⟨ comp t₃ c , s , comp-env ρ ⟩)        ≈⟨ ⟦⟧-correct t₃ _ s-ok c-ok ⟩∼

    run (⟦ t₃ ⟧ ρ >>= k)                             ∼⟨⟩

    run (⟦if⟧ (T.con false) t₂ t₃ ρ >>= k)           ∎

-- Compiler correctness. Note that the equality that is used here is
-- syntactic.

correct :
  ∀ {p} (t : Tm p 0) →
  run (exec ⟨ comp t [] , [] , [] ⟩) ≈
  run (⟦ t ⟧ [] >>= λ v → return (comp-val v))
correct t =
  run (exec ⟨ comp t [] , [] , [] ⟩)            ∼⟨⟩
  run (exec ⟨ comp t [] , [] , comp-env [] ⟩)   ≈⟨ ⟦⟧-correct t [] []-ok (λ v → laterˡ (return (just (comp-val v)) ∎)) ⟩
  run (⟦ t ⟧ [] >>= λ v → return (comp-val v))  ∎
