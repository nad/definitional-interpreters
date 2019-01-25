------------------------------------------------------------------------
-- The "time complexity" of the compiled program matches the one
-- obtained from the instrumented interpreter
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Prelude hiding (_+_; _*_)

import Lambda.Syntax

module Lambda.Compiler-correctness.Steps-match
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm 1)
  where

open import Conat
  using (Conat; zero; suc; force; ⌜_⌝; _+_; _*_; max;
         [_]_≤_; step-≤; step-∼≤; _∎≤)
import Equality.Propositional as E
open import Logical-equivalence using (_⇔_)
import Tactic.By as By
open import Size

open import Function-universe E.equality-with-J hiding (_∘_)
open import List E.equality-with-J using (_++_)
open import Monad E.equality-with-J using (return; _>>=_; _⟨$⟩_)
open import Vec.Data E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity
open import Delay-monad.Quantitative-weak-bisimilarity

open import Lambda.Compiler def
open import Lambda.Delay-crash
open import Lambda.Interpreter.Steps def
open import Lambda.Virtual-machine.Instructions Name hiding (crash)
open import Lambda.Virtual-machine comp-name

private
  module C = Closure Code
  module T = Closure Tm

------------------------------------------------------------------------
-- Some lemmas

-- A rearrangement lemma for ⟦_⟧.

⟦⟧-· :
  ∀ {n} (t₁ t₂ : Tm n) {ρ} {k : T.Value → Delay-crash C.Value ∞} →
  ⟦ t₁ · t₂ ⟧ ρ >>= k ∼
  ⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k
⟦⟧-· t₁ t₂ {ρ} {k} =
  ⟦ t₁ · t₂ ⟧ ρ >>= k      ∼⟨⟩

  (do v₁ ← ⟦ t₁ ⟧ ρ
      v₂ ← ⟦ t₂ ⟧ ρ
      v₁ ∙ v₂) >>= k       ∼⟨ symmetric (associativity (⟦ t₁ ⟧ _) _ _) ⟩

  (do v₁ ← ⟦ t₁ ⟧ ρ
      (do v₂ ← ⟦ t₂ ⟧ ρ
          v₁ ∙ v₂) >>= k)  ∼⟨ (⟦ t₁ ⟧ _ ∎) >>=-cong (λ _ → symmetric (associativity (⟦ t₂ ⟧ _) _ _)) ⟩

  (do v₁ ← ⟦ t₁ ⟧ ρ
      v₂ ← ⟦ t₂ ⟧ ρ
      v₁ ∙ v₂ >>= k)       ∎

-- Lemmas related to conatural numbers.

private

  lemma₁ : ∀ {δ} → [ ∞ ] δ ≤ ⌜ 1 ⌝ + δ
  lemma₁ = Conat.≤suc

  lemma₂ : ∀ {δ} → [ ∞ ] δ ≤ max ⌜ 1 ⌝ δ
  lemma₂ = Conat.ʳ≤max ⌜ 1 ⌝ _

  lemma₃ : ∀ {δ} → [ ∞ ] max ⌜ 1 ⌝ δ ≤ max ⌜ 1 ⌝ δ + ⌜ 1 ⌝
  lemma₃ = Conat.m≤m+n

  lemma₄ : ∀ {δ} → [ ∞ ] δ ≤ max ⌜ 1 ⌝ δ + ⌜ 1 ⌝
  lemma₄ {δ} =
    δ                    ≤⟨ lemma₂ ⟩
    max ⌜ 1 ⌝ δ          ≤⟨ lemma₃ {δ = δ} ⟩
    max ⌜ 1 ⌝ δ + ⌜ 1 ⌝  ∎≤

  lemma₅ : ∀ {δ} → [ ∞ ] ⌜ 1 ⌝ + δ ≤ δ + ⌜ 1 ⌝
  lemma₅ {δ} =
    ⌜ 1 ⌝ + δ  ∼⟨ Conat.+-comm ⌜ 1 ⌝ ⟩≤
    δ + ⌜ 1 ⌝  ∎≤

  lemma₆ : ∀ {δ} → [ ∞ ] ⌜ 1 ⌝ + δ ≤ max ⌜ 1 ⌝ δ + ⌜ 1 ⌝
  lemma₆ {δ} =
    ⌜ 1 ⌝ + δ            ≤⟨ lemma₅ ⟩
    δ + ⌜ 1 ⌝            ≤⟨ lemma₂ Conat.+-mono (⌜ 1 ⌝ ∎≤) ⟩
    max ⌜ 1 ⌝ δ + ⌜ 1 ⌝  ∎≤

  lemma₇ : ∀ {δ} → [ ∞ ] max ⌜ 1 ⌝ (⌜ 1 ⌝ + δ) ≤ ⌜ 1 ⌝ + δ
  lemma₇ {δ} = suc λ { .force →
    δ  ∎≤ }

  lemma₈ : ∀ {δ} → [ ∞ ] max ⌜ 1 ⌝ (max ⌜ 1 ⌝ δ) ≤ max ⌜ 1 ⌝ δ
  lemma₈ {δ} = suc λ { .force →
    Conat.pred δ  ∎≤ }

  lemma₉ :
    ∀ {δ} → [ ∞ ] max ⌜ 1 ⌝ (max ⌜ 1 ⌝ (max ⌜ 1 ⌝ δ)) ≤ max ⌜ 1 ⌝ δ
  lemma₉ {δ} =
    max ⌜ 1 ⌝ (max ⌜ 1 ⌝ (max ⌜ 1 ⌝ δ)) ≤⟨ lemma₈ ⟩
    max ⌜ 1 ⌝ (max ⌜ 1 ⌝ δ)             ≤⟨ lemma₈ ⟩
    max ⌜ 1 ⌝ δ                         ∎≤

  lemma₁₀ : ∀ {δ} → [ ∞ ] ⌜ 1 ⌝ + ⌜ 0 ⌝ ≤ max ⌜ 1 ⌝ δ
  lemma₁₀ = suc λ { .force → zero }

  lemma₁₁ : Conat.[ ∞ ] max ⌜ 1 ⌝ ⌜ 1 ⌝ ∼ ⌜ 1 ⌝
  lemma₁₁ = suc λ { .force → zero }

  lemma₁₂ : Conat.[ ∞ ] ⌜ 1 ⌝ + ⌜ 1 ⌝ ∼ ⌜ 2 ⌝
  lemma₁₂ = Conat.symmetric-∼ (Conat.⌜⌝-+ 1)

------------------------------------------------------------------------
-- Well-formed continuations and stacks

-- A continuation is OK with respect to a certain state and conatural
-- number if the following property is satisfied.

Cont-OK :
  Size → State → (T.Value → Delay-crash C.Value ∞) → Conat ∞ → Set
Cont-OK i ⟨ c , s , ρ ⟩ k δ =
  ∀ v → [ i ∣ ⌜ 1 ⌝ ∣ δ ] exec ⟨ c , val (comp-val v) ∷ s , ρ ⟩ ≳ k v

-- If the In-tail-context parameter indicates that we are in a tail
-- context, then the stack must have a certain shape, and it must be
-- related to the continuation and the conatural number in a certain
-- way.

data Stack-OK
       (i : Size) (k : T.Value → Delay-crash C.Value ∞) (δ : Conat ∞) :
       In-tail-context → Stack → Set where
  unrestricted : ∀ {s} → Stack-OK i k δ false s
  restricted   : ∀ {s n} {c : Code n} {ρ : C.Env n} →
                 Cont-OK i ⟨ c , s , ρ ⟩ k δ →
                 Stack-OK i k δ true (ret c ρ ∷ s)

-- A lemma that can be used to show that certain stacks are OK.

ret-ok :
  ∀ {p i s n c} {ρ : C.Env n} {k δ} →
  Cont-OK i ⟨ c , s , ρ ⟩ k δ →
  Stack-OK i k (⌜ 1 ⌝ + δ) p (ret c ρ ∷ s)
ret-ok {true}  c-ok = restricted (weakenˡ lemma₁ ∘ c-ok)
ret-ok {false} _    = unrestricted

------------------------------------------------------------------------
-- The semantics of the compiled program matches that of the source
-- code

mutual

  -- Some lemmas making up the main part of the compiler correctness
  -- result.

  ⟦⟧-correct :
    ∀ {i n} (t : Tm n) (ρ : T.Env n) {c s}
      {k : T.Value → Delay-crash C.Value ∞} {tc δ} →
    Stack-OK i k δ tc s →
    Cont-OK i ⟨ c , s , comp-env ρ ⟩ k δ →
    [ i ∣ ⌜ 1 ⌝ ∣ max ⌜ 1 ⌝ δ ]
      exec ⟨ comp tc t c , s , comp-env ρ ⟩ ≳ ⟦ t ⟧ ρ >>= k

  ⟦⟧-correct (var x) ρ {c} {s} {k} _ c-ok =
    exec ⟨ var x ∷ c , s , comp-env ρ ⟩                              ≳⟨ later (λ { .force →
      exec ⟨ c , val By.⟨ index x (comp-env ρ) ⟩ ∷ s , comp-env ρ ⟩       ≡⟨ By.⟨by⟩ (comp-index x ρ) ⟩ˢ
      exec ⟨ c , val (comp-val (index x ρ)) ∷ s , comp-env ρ ⟩            ≳⟨ weakenˡ lemma₄ (c-ok (index x ρ)) ⟩ˢ
      k (index x ρ)                                                       ∎ }) ⟩ˢ
    ⟦ var x ⟧ ρ >>= k                                                ∎

  ⟦⟧-correct (lam t) ρ {c} {s} {k} _ c-ok =
    exec ⟨ clo (comp-body t) ∷ c , s , comp-env ρ ⟩             ≳⟨ later (λ { .force →
      exec ⟨ c , val (comp-val (T.lam t ρ)) ∷ s , comp-env ρ ⟩       ≳⟨ weakenˡ lemma₄ (c-ok (T.lam t ρ)) ⟩ˢ
      k (T.lam t ρ)                                                  ∎ }) ⟩ˢ
    ⟦ lam t ⟧ ρ >>= k                                           ∎

  ⟦⟧-correct (t₁ · t₂) ρ {c} {s} {k} _ c-ok =
    exec ⟨ comp false t₁ (comp false t₂ (app ∷ c))
         , s
         , comp-env ρ
         ⟩                                                   ≳⟨ weakenˡ lemma₉ (⟦⟧-correct t₁ _ unrestricted λ v₁ →

      exec ⟨ comp false t₂ (app ∷ c)
           , val (comp-val v₁) ∷ s
           , comp-env ρ
           ⟩                                                       ≳⟨ (⟦⟧-correct t₂ _ unrestricted λ v₂ →

        exec ⟨ app ∷ c
             , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
             , comp-env ρ
             ⟩                                                           ≳⟨ ∙-correct v₁ v₂ c-ok ⟩ˢ

        v₁ ∙ v₂ >>= k                                                    ∎) ⟩ˢ

      (⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k)                          ∎) ⟩ˢ

    (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k)  ∼⟨ symmetric (⟦⟧-· t₁ t₂) ⟩

    ⟦ t₁ · t₂ ⟧ ρ >>= k                                      ∎

  ⟦⟧-correct (call f t) ρ {c} {s} {k} unrestricted c-ok =
    exec ⟨ comp false (call f t) c , s , comp-env ρ ⟩         ∼⟨⟩ˢ

    exec ⟨ comp false t (cal f ∷ c) , s , comp-env ρ ⟩        ≳⟨ (⟦⟧-correct t _ unrestricted λ v →

      exec ⟨ cal f ∷ c , val (comp-val v) ∷ s , comp-env ρ ⟩        ≳⟨ (later λ { .force → weakenˡ lemma₅ (

        exec ⟨ comp-name f
             , ret c (comp-env ρ) ∷ s
             , comp-val v ∷ []
             ⟩                                                            ≳⟨ body-lemma (def f) [] c-ok ⟩ˢ

        (⟦ def f ⟧ (v ∷ []) >>= k)                                        ∎) }) ⟩ˢ

      (T.lam (def f) [] ∙ v >>= k)                                  ∎) ⟩ˢ

    (⟦ t ⟧ ρ >>= λ v → T.lam (def f) [] ∙ v >>= k)            ∼⟨ associativity (⟦ t ⟧ ρ) _ _ ⟩

    (⟦ t ⟧ ρ >>= λ v → T.lam (def f) [] ∙ v) >>= k            ∼⟨⟩

    ⟦ call f t ⟧ ρ >>= k                                      ∎

  ⟦⟧-correct (call f t) ρ {c} {ret c′ ρ′ ∷ s} {k} (restricted c-ok) _ =
    exec ⟨ comp true (call f t) c , ret c′ ρ′ ∷ s , comp-env ρ ⟩    ∼⟨⟩ˢ

    exec ⟨ comp false t (tcl f ∷ c) , ret c′ ρ′ ∷ s , comp-env ρ ⟩  ≳⟨ (⟦⟧-correct t _ unrestricted λ v →

      exec ⟨ tcl f ∷ c
           , val (comp-val v) ∷ ret c′ ρ′ ∷ s
           , comp-env ρ
           ⟩                                                              ≳⟨ (later λ { .force → weakenˡ lemma₅ (

        exec ⟨ comp-name f
             , ret c′ ρ′ ∷ s
             , comp-val v ∷ []
             ⟩                                                                  ≳⟨ body-lemma (def f) [] c-ok ⟩ˢ

        ⟦ def f ⟧ (v ∷ []) >>= k                                                ∎) }) ⟩ˢ

      T.lam (def f) [] ∙ v >>= k                                          ∎) ⟩ˢ

    (⟦ t ⟧ ρ >>= λ v → T.lam (def f) [] ∙ v >>= k)                  ∼⟨ associativity (⟦ t ⟧ ρ) _ _ ⟩

    (⟦ t ⟧ ρ >>= λ v → T.lam (def f) [] ∙ v) >>= k                  ∼⟨⟩

    ⟦ call f t ⟧ ρ >>= k                                            ∎

  ⟦⟧-correct (con b) ρ {c} {s} {k} _ c-ok =
    exec ⟨ con b ∷ c , s , comp-env ρ ⟩                       ≳⟨ later (λ { .force →
      exec ⟨ c , val (comp-val (T.con b)) ∷ s , comp-env ρ ⟩       ≳⟨ weakenˡ lemma₄ (c-ok (T.con b)) ⟩ˢ
      k (T.con b)                                                  ∎ }) ⟩ˢ
    ⟦ con b ⟧ ρ >>= k                                         ∎

  ⟦⟧-correct (if t₁ t₂ t₃) ρ {c} {s} {k} {tc} s-ok c-ok =
    exec ⟨ comp false t₁ (bra (comp tc t₂ []) (comp tc t₃ []) ∷ c)
         , s
         , comp-env ρ
         ⟩                                                          ≳⟨ weakenˡ lemma₈
                                                                         (⟦⟧-correct t₁ _ unrestricted λ v₁ → ⟦if⟧-correct v₁ t₂ t₃ s-ok c-ok) ⟩ˢ

    (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦if⟧ v₁ t₂ t₃ ρ >>= k)                     ∼⟨ associativity (⟦ t₁ ⟧ ρ) _ _ ⟩

    (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦if⟧ v₁ t₂ t₃ ρ) >>= k                     ∼⟨⟩

    ⟦ if t₁ t₂ t₃ ⟧ ρ >>= k                                         ∎

  body-lemma :
    ∀ {i n n′} (t : Tm (suc n)) ρ {ρ′ : C.Env n′} {c s v}
      {k : T.Value → Delay-crash C.Value ∞} {δ} →
    Cont-OK i ⟨ c , s , ρ′ ⟩ k δ →
    [ i ∣ ⌜ 1 ⌝ ∣ ⌜ 1 ⌝ + δ ]
      exec ⟨ comp-body t , ret c ρ′ ∷ s , comp-val v ∷ comp-env ρ ⟩ ≳
      ⟦ t ⟧ (v ∷ ρ) >>= k
  body-lemma t ρ {ρ′} {c} {s} {v} {k} c-ok =
    exec ⟨ comp-body t , ret c ρ′ ∷ s , comp-val v ∷ comp-env ρ ⟩  ∼⟨⟩ˢ

    exec ⟨ comp-body t , ret c ρ′ ∷ s , comp-env (v ∷ ρ) ⟩         ≳⟨ weakenˡ lemma₇ (⟦⟧-correct t (_ ∷ _) (ret-ok c-ok) λ v′ →

      exec ⟨ ret ∷ []
           , val (comp-val v′) ∷ ret c ρ′ ∷ s
           , comp-env (v ∷ ρ)
           ⟩                                                            ≳⟨⟩ˢ

      exec ⟨ c , val (comp-val v′) ∷ s , ρ′ ⟩                           ≳⟨ c-ok v′ ⟩ˢ

      k v′                                                              ∎) ⟩ˢ

    ⟦ t ⟧ (v ∷ ρ) >>= k                                            ∎

  ∙-correct :
    ∀ {i n} v₁ v₂ {ρ : C.Env n} {c s}
      {k : T.Value → Delay-crash C.Value ∞} {δ} →
    Cont-OK i ⟨ c , s , ρ ⟩ k δ →
    [ i ∣ ⌜ 1 ⌝ ∣ max ⌜ 1 ⌝ δ ]
      exec ⟨ app ∷ c , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s , ρ ⟩ ≳
      v₁ ∙ v₂ >>= k

  ∙-correct (T.lam t₁ ρ₁) v₂ {ρ} {c} {s} {k} c-ok =
    exec ⟨ app ∷ c
         , val (comp-val v₂) ∷ val (comp-val (T.lam t₁ ρ₁)) ∷ s
         , ρ
         ⟩                                                             ≳⟨ later (λ { .force → weakenˡ lemma₆ (

      exec ⟨ comp-body t₁ , ret c ρ ∷ s , comp-val v₂ ∷ comp-env ρ₁ ⟩       ≳⟨ body-lemma t₁ _ c-ok ⟩ˢ

      ⟦ t₁ ⟧ (v₂ ∷ ρ₁) >>= k                                                ∎) }) ⟩ˢ

    T.lam t₁ ρ₁ ∙ v₂ >>= k                                             ∎

  ∙-correct (T.con b) v₂ {ρ} {c} {s} {k} _ = weakenˡ lemma₁₀ (
    exec ⟨ app ∷ c
         , val (comp-val v₂) ∷ val (comp-val (T.con b)) ∷ s
         , ρ
         ⟩                                                   ≳⟨⟩ˢ

    crash                                                    ∼⟨⟩ˢ

    T.con b ∙ v₂ >>= k                                       ∎ˢ)

  ⟦if⟧-correct :
    ∀ {i n} v₁ (t₂ t₃ : Tm n) {ρ : T.Env n} {c s}
      {k : T.Value → Delay-crash C.Value ∞} {tc δ} →
    Stack-OK i k δ tc s →
    Cont-OK i ⟨ c , s , comp-env ρ ⟩ k δ →
    [ i ∣ ⌜ 1 ⌝ ∣ max ⌜ 1 ⌝ δ ]
      exec ⟨ bra (comp tc t₂ []) (comp tc t₃ []) ∷ c
           , val (comp-val v₁) ∷ s
           , comp-env ρ
           ⟩ ≳
      ⟦if⟧ v₁ t₂ t₃ ρ >>= k

  ⟦if⟧-correct (T.lam t₁ ρ₁) t₂ t₃ {ρ} {c} {s} {k} {tc} _ _ =
    weakenˡ lemma₁₀ (

      exec ⟨ bra (comp tc t₂ []) (comp tc t₃ []) ∷ c
           , val (comp-val (T.lam t₁ ρ₁)) ∷ s
           , comp-env ρ
           ⟩                                          ≳⟨⟩ˢ

      crash                                           ∼⟨⟩ˢ

      ⟦if⟧ (T.lam t₁ ρ₁) t₂ t₃ ρ >>= k                ∎ˢ)

  ⟦if⟧-correct (T.con true) t₂ t₃ {ρ} {c} {s} {k} {tc} s-ok c-ok =
    exec ⟨ bra (comp tc t₂ []) (comp tc t₃ []) ∷ c
         , val (comp-val (T.con true)) ∷ s
         , comp-env ρ
         ⟩                                          ≳⟨ later (λ { .force → weakenˡ lemma₃ (

      exec ⟨ comp tc t₂ [] ++ c , s , comp-env ρ ⟩       ≡⟨ By.by (comp-++ _ t₂) ⟩ˢ

      exec ⟨ comp tc t₂ c , s , comp-env ρ ⟩             ≳⟨ ⟦⟧-correct t₂ _ s-ok c-ok ⟩ˢ

      ⟦ t₂ ⟧ ρ >>= k                                     ∎) }) ⟩ˢ

    ⟦if⟧ (T.con true) t₂ t₃ ρ >>= k                 ∎

  ⟦if⟧-correct (T.con false) t₂ t₃ {ρ} {c} {s} {k} {tc} s-ok c-ok =
    exec ⟨ bra (comp tc t₂ []) (comp tc t₃ []) ∷ c
         , val (comp-val (T.con false)) ∷ s
         , comp-env ρ
         ⟩                                          ≳⟨ later (λ { .force → weakenˡ lemma₃ (

      exec ⟨ comp tc t₃ [] ++ c , s , comp-env ρ ⟩       ≡⟨ By.by (comp-++ _ t₃) ⟩ˢ

      exec ⟨ comp tc t₃ c , s , comp-env ρ ⟩             ≳⟨ ⟦⟧-correct t₃ _ s-ok c-ok ⟩ˢ

      ⟦ t₃ ⟧ ρ >>= k                                     ∎) }) ⟩ˢ

    ⟦if⟧ (T.con false) t₂ t₃ ρ >>= k                ∎

-- The "time complexity" of the compiled program is linear in the time
-- complexity obtained from the instrumented interpreter, and vice
-- versa.

steps-match :
  (t : Tm 0) →
  [ ∞ ] steps (⟦ t ⟧ []) ≤ steps (exec ⟨ comp₀ t , [] , [] ⟩)
    ×
  [ ∞ ] steps (exec ⟨ comp₀ t , [] , [] ⟩) ≤
        ⌜ 1 ⌝ + ⌜ 2 ⌝ * steps (⟦ t ⟧ [])
steps-match t =                                                  $⟨ ⟦⟧-correct t [] unrestricted (λ v → laterˡ (return (comp-val v) ∎ˢ)) ⟩
  [ ∞ ∣ ⌜ 1 ⌝ ∣ max ⌜ 1 ⌝ ⌜ 1 ⌝ ]
    exec ⟨ comp₀ t , [] , [] ⟩ ≳ comp-val ⟨$⟩ ⟦ t ⟧ []           ↝⟨ proj₂ ∘ _⇔_.to ≳⇔≈×steps≤steps² ⟩

  [ ∞ ] steps (comp-val ⟨$⟩ ⟦ t ⟧ []) ≤
        steps (exec ⟨ comp₀ t , [] , [] ⟩) ×
  [ ∞ ] steps (exec ⟨ comp₀ t , [] , [] ⟩) ≤
        max ⌜ 1 ⌝ ⌜ 1 ⌝ +
        (⌜ 1 ⌝ + ⌜ 1 ⌝) * steps (comp-val ⟨$⟩ ⟦ t ⟧ [])          ↝⟨ _⇔_.to (steps-⟨$⟩ Conat.≤-cong-∼ (_ Conat.∎∼)
                                                                              ×-cong
                                                                            (_ Conat.∎∼)
                                                                              Conat.≤-cong-∼
                                                                            lemma₁₁ Conat.+-cong lemma₁₂ Conat.*-cong steps-⟨$⟩) ⟩□
  [ ∞ ] steps (⟦ t ⟧ []) ≤ steps (exec ⟨ comp₀ t , [] , [] ⟩) ×
  [ ∞ ] steps (exec ⟨ comp₀ t , [] , [] ⟩) ≤
        ⌜ 1 ⌝ + ⌜ 2 ⌝ * steps (⟦ t ⟧ [])                         □
