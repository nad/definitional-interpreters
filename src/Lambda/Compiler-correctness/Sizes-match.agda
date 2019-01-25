------------------------------------------------------------------------
-- The actual maximum stack size of the compiled program matches the
-- maximum stack size of the instrumented source-level semantics
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Prelude

import Lambda.Syntax

module Lambda.Compiler-correctness.Sizes-match
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm 1)
  where

open import Colist hiding (_++_; length)
import Conat
open import Equality.Propositional as E using (refl)
open import Logical-equivalence using (_⇔_)
open import Tactic.By using (by)
open import Size

open import Function-universe E.equality-with-J hiding (id; _∘_)
open import List E.equality-with-J using (_++_; length)
open import Monad E.equality-with-J
open import Nat E.equality-with-J
open import Vec.Data E.equality-with-J

open import Upper-bounds

open import Lambda.Compiler def
open import Lambda.Interpreter.Stack-sizes def as I
open import Lambda.Delay-crash-trace as DCT
  using (Delay-crash-trace)
open import Lambda.Virtual-machine.Instructions Name
open import Lambda.Virtual-machine comp-name as VM

private
  module C = Closure Code
  module T = Closure Tm

open Delay-crash-trace using (tell)

------------------------------------------------------------------------
-- A lemma

-- A rearrangement lemma for ⟦_⟧⁺.

⟦⟧-· :
  ∀ {A n} (t₁ t₂ : Tm n)
    {ρ} tc {k : T.Value → Delay-crash-trace (ℕ → ℕ) A ∞} →
  DCT.[ ∞ ] ⟦ t₁ · t₂ ⟧ ρ tc >>= k ∼
            do v₁ ← ⟦ t₁ ⟧ ρ false
               v₂ ← ⟦ t₂ ⟧ ρ false
               [ pred , pred ] v₁ ∙ v₂ >>= k
⟦⟧-· t₁ t₂ {ρ} tc {k} =
  ⟦ t₁ · t₂ ⟧ ρ tc >>= k                   DCT.∼⟨⟩

  (do v₁ ← ⟦ t₁ ⟧ ρ false
      v₂ ← ⟦ t₂ ⟧ ρ false
      [ pred , pred ] v₁ ∙ v₂) >>= k       DCT.∼⟨ DCT.symmetric (DCT.associativity (⟦ t₁ ⟧ _ _) _ _) ⟩

  (do v₁ ← ⟦ t₁ ⟧ ρ false
      (do v₂ ← ⟦ t₂ ⟧ ρ false
          [ pred , pred ] v₁ ∙ v₂) >>= k)  DCT.∼⟨ ((⟦ t₁ ⟧ _ _ DCT.∎) DCT.>>=-cong λ _ → DCT.symmetric (DCT.associativity (⟦ t₂ ⟧ _ _) _ _)) ⟩

  (do v₁ ← ⟦ t₁ ⟧ ρ false
      v₂ ← ⟦ t₂ ⟧ ρ false
      [ pred , pred ] v₁ ∙ v₂ >>= k)       DCT.∎

------------------------------------------------------------------------
-- Well-formed continuations and stacks

-- A continuation is OK with respect to a certain state if the
-- following property is satisfied.

Cont-OK :
  Size → State → (T.Value → Delay-crash-trace (ℕ → ℕ) C.Value ∞) → Set
Cont-OK i ⟨ c , s , ρ ⟩ k =
  ∀ v → [ i ] VM.stack-sizes ⟨ c , val (comp-val v) ∷ s , ρ ⟩ ≂
              numbers (k v) (1 + length s)

-- A workaround for what might be an Agda bug.

castC :
  ∀ {i} {j : Size< i} {s k} →
  Cont-OK i s k → Cont-OK j s k
castC {s = ⟨ _ , _ , _ ⟩} c-ok = cast-≂ ∘ c-ok

-- If the In-tail-context parameter indicates that we are in a tail
-- context, then the stack must have a certain shape, and it must be
-- related to the continuation in a certain way.

data Stack-OK (i : Size)
              (k : T.Value → Delay-crash-trace (ℕ → ℕ) C.Value ∞) :
              In-tail-context → Stack → Set where
  unrestricted : ∀ {s} → Stack-OK i k false s
  restricted   :
    ∀ {s n} {c : Code n} {ρ : C.Env n} →
    (∀ v → [ i ] 2 + length s ∷′
                 VM.stack-sizes ⟨ c , val (comp-val v) ∷ s , ρ ⟩ ≂
                 numbers (k v) (2 + length s)) →
    Stack-OK i k true (ret c ρ ∷ s)

-- Stacks that are OK in a tail context are OK in any context.

any-OK :
  ∀ {tc i k s} →
  Stack-OK i k true s →
  Stack-OK i k tc   s
any-OK {false} = const unrestricted
any-OK {true}  = id

------------------------------------------------------------------------
-- The stack sizes match

mutual

  -- Some lemmas making up the main part of the correctness result.

  ⟦⟧-correct :
    ∀ {i n} (t : Tm n) (ρ : T.Env n) {tc c s}
      {k : T.Value → Delay-crash-trace (ℕ → ℕ) C.Value ∞} →
    Stack-OK i k tc s →
    Cont-OK i ⟨ c , s , comp-env ρ ⟩ k →
    [ i ] VM.stack-sizes ⟨ comp tc t c , s , comp-env ρ ⟩ ≂
          numbers (⟦ t ⟧ ρ tc >>= k) (length s)

  ⟦⟧-correct (var x) ρ {tc} {c} {s} {k} _ c-ok =
    VM.stack-sizes ⟨ var x ∷ c , s , comp-env ρ ⟩                         ∼⟨ ∷∼∷′ ⟩≂

    (length s ∷′
     VM.stack-sizes ⟨ c , val (index x (comp-env ρ)) ∷ s , comp-env ρ ⟩)  ≡⟨ by (comp-index x ρ) ⟩≂

    (length s ∷′
     VM.stack-sizes ⟨ c , val (comp-val (index x ρ)) ∷ s , comp-env ρ ⟩)  ≂⟨ cons″-≂ (c-ok (index x ρ)) ⟩∼

    (length s ∷′ numbers (k (index x ρ)) (1 + length s))                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦ var x ⟧ ρ tc >>= k) (length s)                             ∎

  ⟦⟧-correct (lam t) ρ {tc} {c} {s} {k} _ c-ok =
    VM.stack-sizes ⟨ clo (comp-body t) ∷ c , s , comp-env ρ ⟩             ∼⟨ ∷∼∷′ ⟩≂

    (length s ∷′
     VM.stack-sizes ⟨ c , val (comp-val (T.lam t ρ)) ∷ s , comp-env ρ ⟩)  ≂⟨ cons″-≂ (c-ok (T.lam t ρ)) ⟩∼

    (length s ∷′ numbers (k (T.lam t ρ)) (1 + length s))                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦ lam t ⟧ ρ tc >>= k) (length s)                             ∎

  ⟦⟧-correct (t₁ · t₂) ρ {tc} {c} {s} {k} _ c-ok =
    VM.stack-sizes ⟨ comp false t₁ (comp false t₂ (app ∷ c))
                   , s
                   , comp-env ρ
                   ⟩                                                ≂⟨ (⟦⟧-correct t₁ _ unrestricted λ v₁ →

      VM.stack-sizes ⟨ comp false t₂ (app ∷ c)
                     , val (comp-val v₁) ∷ s
                     , comp-env ρ
                     ⟩                                                    ≂⟨ (⟦⟧-correct t₂ _ unrestricted λ v₂ →

        VM.stack-sizes ⟨ app ∷ c
                       , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
                       , comp-env ρ
                       ⟩                                                        ≂⟨ ∙-correct v₁ v₂ c-ok ⟩∼

        numbers ([ pred , pred ] v₁ ∙ v₂ >>= k) (2 + length s)                  ∎) ⟩∼

      numbers (do v₂ ← ⟦ t₂ ⟧ ρ false
                  [ pred , pred ] v₁ ∙ v₂ >>= k)
              (1 + length s)                                              ∎) ⟩∼

    numbers (do v₁ ← ⟦ t₁ ⟧ ρ false
                v₂ ← ⟦ t₂ ⟧ ρ false
                [ pred , pred ] v₁ ∙ v₂ >>= k)
            (length s)                                              ∼⟨ symmetric-∼ (numbers-cong (⟦⟧-· t₁ t₂ tc)) ⟩

    numbers (⟦ t₁ · t₂ ⟧ ρ tc >>= k) (length s)                     ∎

  ⟦⟧-correct (call f t) ρ {false} {c} {s} {k} unrestricted c-ok =
    VM.stack-sizes ⟨ comp false t (cal f ∷ c) , s , comp-env ρ ⟩        ≂⟨ (⟦⟧-correct t _ unrestricted λ v →

      VM.stack-sizes ⟨ cal f ∷ c , val (comp-val v) ∷ s , comp-env ρ ⟩        ∼⟨ ∷∼∷′ ⟩≂

      1 + length s ∷′
      VM.stack-sizes ⟨ comp-name f
                     , ret c (comp-env ρ) ∷ s
                     , comp-val v ∷ []
                     ⟩                                                        ≂⟨ cons′-≂ (_⇔_.from ≂′⇔≂″ λ { .force →
                                                                                   body-lemma (def f) [] (castC c-ok) }) ⟩∼
      1 + length s ∷′
      numbers (⟦ def f ⟧ (v ∷ []) true >>= tell pred ∘ return >>= k)
              (1 + length s)                                                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

      numbers ([ id , pred ] T.lam (def f) [] ∙ v >>= k)
              (1 + length s)                                                  ∎) ⟩∼

    numbers (⟦ t ⟧ ρ false >>= λ v →
             [ id , pred ] T.lam (def f) [] ∙ v >>= k)
            (length s)                                                  ∼⟨ numbers-cong (DCT.associativity (⟦ t ⟧ _ _) _ _) ⟩

    numbers ((⟦ t ⟧ ρ false >>=
              [ id , pred ] T.lam (def f) [] ∙_) >>= k)
            (length s)                                                  ∼⟨⟩

    numbers (⟦ call f t ⟧ ρ false >>= k) (length s)                     ∎

  ⟦⟧-correct {i} (call f t) ρ {true} {c} {ret c′ ρ′ ∷ s} {k}
             s-ok@(restricted c-ok) _ =
    VM.stack-sizes ⟨ comp false t (tcl f ∷ c)
                   , ret c′ ρ′ ∷ s
                   , comp-env ρ
                   ⟩                                                    ≂⟨ (⟦⟧-correct t _ unrestricted λ v →

      VM.stack-sizes ⟨ tcl f ∷ c
                     , val (comp-val v) ∷ ret c′ ρ′ ∷ s
                     , comp-env ρ
                     ⟩                                                        ∼⟨ ∷∼∷′ ⟩≂

      2 + length s ∷′
      VM.stack-sizes ⟨ comp-name f
                     , ret c′ ρ′ ∷ s
                     , comp-val v ∷ []
                     ⟩                                                        ≡⟨⟩≂

      2 + length s ∷′
      VM.stack-sizes ⟨ comp-name f
                     , ret c′ ρ′ ∷ s
                     , comp-env (v ∷ [])
                     ⟩                                                        ≂⟨ cons′-≂ (_⇔_.from ≂′⇔≂″ λ { .force →
                                                                                   ⟦⟧-correct (def f) (_ ∷ []) (restricted lemma) (λ v′ →
        VM.stack-sizes ⟨ ret ∷ []
                       , val (comp-val v′) ∷ ret c′ ρ′ ∷ s
                       , comp-env (v ∷ [])
                       ⟩                                                             ∼⟨ ∷∼∷′ ⟩≂

        2 + length s ∷′
        VM.stack-sizes ⟨ c′ , val (comp-val v′) ∷ s , ρ′ ⟩                           ≂⟨ lemma v′ ⟩∼

        numbers (tell id (k v′)) (2 + length s)                                      ∎) }) ⟩∼

      2 + length s ∷′
      numbers (⟦ def f ⟧ (v ∷ []) true >>= tell id ∘ k) (1 + length s)        ∼⟨ (refl ∷ λ { .force →
                                                                                  numbers-cong (DCT.associativity (⟦ def f ⟧ _ _) _ _) }) ⟩
      2 + length s ∷′
      numbers (⟦ def f ⟧ (v ∷ []) true >>= tell id ∘ return >>= k)
              (1 + length s)                                                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

      numbers ([ pred , id ] T.lam (def f) [] ∙ v >>= k)
              (2 + length s)                                                  ∎) ⟩∼

    numbers (⟦ t ⟧ ρ false >>= λ v →
             [ pred , id ] T.lam (def f) [] ∙ v >>= k)
            (1 + length s)                                              ∼⟨ numbers-cong (DCT.associativity (⟦ t ⟧ _ _) _ _) ⟩

    numbers ((⟦ t ⟧ ρ false >>=
              [ pred , id ] T.lam (def f) [] ∙_) >>= k)
            (1 + length s)                                              ∼⟨⟩

    numbers (⟦ call f t ⟧ ρ true >>= k) (1 + length s)                  ∎
    where
    lemma : {j : Size< i} → _
    lemma = λ v′ →
      2 + length s ∷′
      VM.stack-sizes ⟨ c′ , val (comp-val v′) ∷ s , ρ′ ⟩  ≂⟨ consʳ-≂ (inj₁ (here ≤-refl)) (cast-≂ (c-ok v′)) ⟩∼

      2 + length s ∷′
      numbers (k v′) (2 + length s)                       ∼⟨ symmetric-∼ ∷∼∷′ ⟩

      numbers (tell id (k v′)) (2 + length s)             ∎

  ⟦⟧-correct (con b) ρ {tc} {c} {s} {k} _ c-ok =
    VM.stack-sizes ⟨ con b ∷ c , s , comp-env ρ ⟩                       ∼⟨ ∷∼∷′ ⟩≂

    (length s ∷′
     VM.stack-sizes ⟨ c , val (comp-val (T.con b)) ∷ s , comp-env ρ ⟩)  ≂⟨ cons″-≂ (c-ok (T.con b)) ⟩∼

    (length s ∷′ numbers (k (T.con b)) (1 + length s))                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦ con b ⟧ ρ tc >>= k) (length s)                           ∎

  ⟦⟧-correct (if t₁ t₂ t₃) ρ {tc} {c} {s} {k} s-ok c-ok =
    VM.stack-sizes ⟨ comp false t₁
                       (bra (comp tc t₂ []) (comp tc t₃ []) ∷ c)
                   , s
                   , comp-env ρ
                   ⟩                                                ≂⟨ (⟦⟧-correct t₁ _ unrestricted λ v₁ → ⟦if⟧-correct v₁ t₂ t₃ s-ok c-ok) ⟩∼

    numbers (⟦ t₁ ⟧ ρ false >>= λ v₁ → ⟦if⟧ v₁ t₂ t₃ ρ tc >>= k)
            (length s)                                              ∼⟨ numbers-cong (DCT.associativity (⟦ t₁ ⟧ _ _) _ _) ⟩

    numbers ((⟦ t₁ ⟧ ρ false >>= λ v₁ → ⟦if⟧ v₁ t₂ t₃ ρ tc) >>= k)
            (length s)                                              ∎

  body-lemma :
    ∀ {i n n′} (t : Tm (1 + n)) ρ {ρ′ : C.Env n′} {c s v}
      {k : T.Value → Delay-crash-trace (ℕ → ℕ) C.Value ∞} →
    Cont-OK i ⟨ c , s , ρ′ ⟩ k →
    [ i ] VM.stack-sizes ⟨ comp-body t
                         , ret c ρ′ ∷ s
                         , comp-val v ∷ comp-env ρ
                         ⟩ ≂
          numbers (⟦ t ⟧ (v ∷ ρ) true >>= tell pred ∘ return >>= k)
                  (1 + length s)
  body-lemma t ρ {ρ′} {c} {s} {v} {k} c-ok =
    VM.stack-sizes ⟨ comp-body t
                   , ret c ρ′ ∷ s
                   , comp-val v ∷ comp-env ρ
                   ⟩                                               ≡⟨⟩≂

    VM.stack-sizes ⟨ comp-body t
                   , ret c ρ′ ∷ s
                   , comp-env (v ∷ ρ)
                   ⟩                                               ≂⟨ (⟦⟧-correct t (_ ∷ _) (any-OK (restricted lemma)) λ v′ →

      VM.stack-sizes ⟨ ret ∷ []
                     , val (comp-val v′) ∷ ret c ρ′ ∷ s
                     , comp-env (v ∷ ρ)
                     ⟩                                                   ∼⟨ ∷∼∷′ ⟩≂

      2 + length s ∷′
      VM.stack-sizes ⟨ c , val (comp-val v′) ∷ s , ρ′ ⟩                  ≂⟨ lemma v′ ⟩∼

      numbers (tell pred (k v′)) (2 + length s)                          ∎) ⟩∼

    numbers (⟦ t ⟧ (v ∷ ρ) true >>= tell pred ∘ k) (1 + length s)  ∼⟨ numbers-cong (DCT.associativity (⟦ t ⟧ _ _) _ _) ⟩

    numbers (⟦ t ⟧ (v ∷ ρ) true >>= tell pred ∘ return >>= k)
            (1 + length s)                                         ∎
    where
    lemma = λ v′ →
      2 + length s ∷′
      VM.stack-sizes ⟨ c , val (comp-val v′) ∷ s , ρ′ ⟩  ≂⟨ cons″-≂ (c-ok v′) ⟩∼

      2 + length s ∷′ numbers (k v′) (1 + length s)      ∼⟨ symmetric-∼ ∷∼∷′ ⟩

      numbers (tell pred (k v′)) (2 + length s)          ∎

  ∙-correct :
    ∀ {i n} v₁ v₂ {ρ : C.Env n} {c s}
      {k : T.Value → Delay-crash-trace (ℕ → ℕ) C.Value ∞} →
    Cont-OK i ⟨ c , s , ρ ⟩ k →
    [ i ] VM.stack-sizes ⟨ app ∷ c
                         , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
                         , ρ
                         ⟩ ≂
          numbers ([ pred , pred ] v₁ ∙ v₂ >>= k) (2 + length s)

  ∙-correct (T.lam t₁ ρ₁) v₂ {ρ} {c} {s} {k} c-ok =
    VM.stack-sizes
      ⟨ app ∷ c
      , val (comp-val v₂) ∷ val (comp-val (T.lam t₁ ρ₁)) ∷ s
      , ρ
      ⟩                                                              ∼⟨ ∷∼∷′ ⟩≂

    2 + length s ∷′
    VM.stack-sizes ⟨ comp-body t₁
                   , ret c ρ ∷ s
                   , comp-val v₂ ∷ comp-env ρ₁
                   ⟩                                                 ≂⟨ cons′-≂ (_⇔_.from ≂′⇔≂″ λ { .force → body-lemma t₁ _ (castC c-ok) }) ⟩∼

    2 + length s ∷′
    numbers (⟦ t₁ ⟧ (v₂ ∷ ρ₁) true >>= tell pred ∘ return >>= k)
            (1 + length s)                                           ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers ([ pred , pred ] T.lam t₁ ρ₁ ∙ v₂ >>= k) (2 + length s)  ∎

  ∙-correct (T.con b) v₂ {ρ} {c} {s} {k} _ =
    VM.stack-sizes ⟨ app ∷ c
                   , val (comp-val v₂) ∷ val (C.con b) ∷ s
                   , ρ
                   ⟩                                             ∼⟨ ∷∼∷′ ⟩≂

    2 + length s ∷′ []                                           ∼⟨ symmetric-∼ ∷∼∷′ ⟩≂

    numbers ([ pred , pred ] T.con b ∙ v₂ >>= k) (2 + length s)  □≂

  ⟦if⟧-correct :
    ∀ {i n} v₁ t₂ t₃ {ρ : T.Env n} {tc c s}
      {k : T.Value → Delay-crash-trace (ℕ → ℕ) C.Value ∞} →
    Stack-OK i k tc s →
    Cont-OK i ⟨ c , s , comp-env ρ ⟩ k →
    [ i ] VM.stack-sizes ⟨ bra (comp tc t₂ []) (comp tc t₃ []) ∷ c
                         , val (comp-val v₁) ∷ s
                         , comp-env ρ
                         ⟩ ≂
          numbers (⟦if⟧ v₁ t₂ t₃ ρ tc >>= k) (1 + length s)

  ⟦if⟧-correct (T.lam t₁ ρ₁) t₂ t₃ {ρ} {tc} {c} {s} {k} _ _ =
    VM.stack-sizes ⟨ bra (comp tc t₂ []) (comp tc t₃ []) ∷ c
                   , val (comp-val (T.lam t₁ ρ₁)) ∷ s
                   , comp-env ρ
                   ⟩                                              ∼⟨ ∷∼∷′ ⟩≂

    1 + length s ∷′ []                                            ∼⟨ symmetric-∼ ∷∼∷′ ⟩≂

    numbers (⟦if⟧ (T.lam t₁ ρ₁) t₂ t₃ ρ tc >>= k) (1 + length s)  □≂

  ⟦if⟧-correct (T.con true) t₂ t₃ {ρ} {tc} {c} {s} {k} s-ok c-ok =
    VM.stack-sizes ⟨ bra (comp tc t₂ []) (comp tc t₃ []) ∷ c
                   , val (comp-val (T.con true)) ∷ s
                   , comp-env ρ
                   ⟩                                             ∼⟨ ∷∼∷′ ⟩≂

    1 + length s ∷′
    VM.stack-sizes ⟨ comp tc t₂ [] ++ c , s , comp-env ρ ⟩       ≡⟨ by (comp-++ _ t₂) ⟩≂

    1 + length s ∷′
    VM.stack-sizes ⟨ comp tc t₂ c , s , comp-env ρ ⟩             ≂⟨ cons″-≂ (⟦⟧-correct t₂ _ s-ok c-ok) ⟩∼

    1 + length s ∷′ numbers (⟦ t₂ ⟧ ρ tc >>= k) (length s)       ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦if⟧ (T.con true) t₂ t₃ ρ tc >>= k) (1 + length s)  ∎

  ⟦if⟧-correct (T.con false) t₂ t₃ {ρ} {tc} {c} {s} {k} s-ok c-ok =
    VM.stack-sizes ⟨ bra (comp tc t₂ []) (comp tc t₃ []) ∷ c
                   , val (comp-val (T.con false)) ∷ s
                   , comp-env ρ
                   ⟩                                              ∼⟨ ∷∼∷′ ⟩≂

    1 + length s ∷′
    VM.stack-sizes ⟨ comp tc t₃ [] ++ c , s , comp-env ρ ⟩        ≡⟨ by (comp-++ _ t₃) ⟩≂

    1 + length s ∷′
    VM.stack-sizes ⟨ comp tc t₃ c , s , comp-env ρ ⟩              ≂⟨ cons″-≂ (⟦⟧-correct t₃ _ s-ok c-ok) ⟩∼

    1 + length s ∷′ numbers (⟦ t₃ ⟧ ρ tc >>= k) (length s)        ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦if⟧ (T.con false) t₂ t₃ ρ tc >>= k) (1 + length s)  ∎

-- The virtual machine and the interpreter produce related lists of
-- stack sizes.
--
-- (However, the traces are not necessarily bisimilar, see
-- Lambda.Interpreter.Stack-sizes.Counterexample.stack-sizes-not-bisimilar.)

stack-sizes-related :
  (t : Tm 0) →
  [ ∞ ] VM.stack-sizes ⟨ comp₀ t , [] , [] ⟩ ≂ I.stack-sizes t
stack-sizes-related t =
  VM.stack-sizes ⟨ comp false t [] , [] , [] ⟩  ≂⟨ ⟦⟧-correct t [] unrestricted (λ _ → cons″-≂ (_ □≂)) ⟩∼
  numbers (comp-val ⟨$⟩ ⟦ t ⟧ [] false) 0       ∼⟨ scanl-cong (DCT.trace-⟨$⟩ _) ⟩
  numbers (⟦ t ⟧ [] false) 0                    ∼⟨⟩
  I.stack-sizes t                               ∎

-- The maximum stack sizes match.

maximum-stack-sizes-match :
  ∀ (t : Tm 0) {i v} →
  LUB (I.stack-sizes t) i →
  LUB (VM.stack-sizes ⟨ comp₀ t , [] , [] ⟩) v →
  Conat.[ ∞ ] i ∼ v
maximum-stack-sizes-match t {i} {v} i-lub =
  LUB (VM.stack-sizes ⟨ comp₀ t , [] , [] ⟩) v  ↝⟨ LUB-≂ (stack-sizes-related t) ⟩
  LUB (I.stack-sizes t) v                       ↝⟨ lub-unique i-lub ⟩□
  Conat.[ ∞ ] i ∼ v                             □
