------------------------------------------------------------------------
-- The actual maximum stack size of the compiled program matches the
-- maximum stack size of the annotated source-level semantics
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Prelude

import Lambda.Syntax

module Lambda.Compiler-correctness.Sizes-match
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm true 1)
  where

open import Colist hiding (_++_)
import Conat
open import Equality.Propositional as E using (refl)
open import Tactic.By using (by)

open import Function-universe E.equality-with-J hiding (id; _∘_)
open import List E.equality-with-J using (_++_; length)
open import Monad E.equality-with-J
open import Nat E.equality-with-J
open import Vec.Data E.equality-with-J

open import Upper-bounds

open import Lambda.Compiler def
open import Lambda.Interpreter.Annotated def as I
open import Lambda.Delay-crash-colist as DCC
  using (Delay-crash-colist; tell)
open import Lambda.Virtual-machine.Instructions Name
open import Lambda.Virtual-machine comp-name as VM

private
  module C = Closure (const Code)
  module T = Closure Tm

------------------------------------------------------------------------
-- A lemma

-- A rearrangement lemma for ⟦_⟧⁺.

⟦⟧⁺-· :
  ∀ {A n} p (t₁ t₂ : Tm false n)
    {ρ} {k : T.Value → Delay-crash-colist (ℕ → ℕ) A ∞} →
  DCC.[ ∞ ] ⟦ _·_ {p = p} t₁ t₂ ⟧⁺ ρ >>= k ∼
            do v₁ ← ⟦ t₁ ⟧⁺ ρ
               v₂ ← ⟦ t₂ ⟧⁺ ρ
               [ pred , just pred ] v₁ ∙⁺ v₂ >>= k
⟦⟧⁺-· p t₁ t₂ {ρ} {k} =
  ⟦ _·_ {p = p} t₁ t₂ ⟧⁺ ρ >>= k                 DCC.∼⟨⟩

  (do v₁ ← ⟦ t₁ ⟧⁺ ρ
      v₂ ← ⟦ t₂ ⟧⁺ ρ
      [ pred , just pred ] v₁ ∙⁺ v₂) >>= k       DCC.∼⟨ DCC.symmetric (DCC.associativity (⟦ t₁ ⟧⁺ _) _ _) ⟩

  (do v₁ ← ⟦ t₁ ⟧⁺ ρ
      (do v₂ ← ⟦ t₂ ⟧⁺ ρ
          [ pred , just pred ] v₁ ∙⁺ v₂) >>= k)  DCC.∼⟨ ((⟦ t₁ ⟧⁺ _ DCC.∎) DCC.>>=-cong λ _ → DCC.symmetric (DCC.associativity (⟦ t₂ ⟧⁺ _) _ _)) ⟩

  (do v₁ ← ⟦ t₁ ⟧⁺ ρ
      v₂ ← ⟦ t₂ ⟧⁺ ρ
      [ pred , just pred ] v₁ ∙⁺ v₂ >>= k)       DCC.∎

------------------------------------------------------------------------
-- Well-formed continuations and stacks

-- A continuation is OK with respect to a certain state if the
-- following property is satisfied.

Cont-OK :
  Size → State → (T.Value → Delay-crash-colist (ℕ → ℕ) C.Value ∞) → Set
Cont-OK i ⟨ c , s , ρ ⟩ k =
  ∀ v → [ i ] VM.stack-sizes ⟨ c , val (comp-val v) ∷ s , ρ ⟩ ∼
              numbers (k v) (1 + length s)

-- If the In-tail-context parameter indicates that we are in a tail
-- context, then the stack must have a certain shape, and it must be
-- related to the continuation in a certain way.

data Stack-OK (i : Size)
              (k : T.Value → Delay-crash-colist (ℕ → ℕ) C.Value ∞) :
              In-tail-context → Stack → Set where
  unrestricted : ∀ {s} → Stack-OK i k false s
  restricted-∷ :
    ∀ {s n c} {ρ : C.Env n} →
    (∀ v → [ i ] 2 + length s ∷′
                 VM.stack-sizes ⟨ c , val (comp-val v) ∷ s , ρ ⟩ ∼
                 numbers (k v) (2 + length s)) →
    Stack-OK i k true (ret c ρ ∷ s)

-- A lemma that can be used to show that certain stacks are OK.

ret-ok :
  ∀ {p i n} {c : Code n} {s ρ k} →
  Cont-OK i ⟨ c , s , ρ ⟩ k →
  Stack-OK i (tell pred ∘ k) p (ret c ρ ∷ s)
ret-ok {false}                    _    = unrestricted
ret-ok {true} {c = c} {s} {ρ} {k} c-ok = restricted-∷ λ v →
  2 + length s ∷′ VM.stack-sizes ⟨ c , val (comp-val v) ∷ s , ρ ⟩  ∼⟨ (refl ∷ λ { .force → c-ok v }) ⟩
  2 + length s ∷′ numbers (k v) (1 + length s)                     ∼⟨ symmetric-∼ ∷∼∷′ ⟩
  numbers (tell pred (k v)) (2 + length s)                         ∎

------------------------------------------------------------------------
-- The stack sizes match

mutual

  -- Some lemmas making up the main part of the correctness result.

  ⟦⟧⁺-correct :
    ∀ {p i n} (t : Tm p n) (ρ : T.Env n) {c s}
      {k : T.Value → Delay-crash-colist (ℕ → ℕ) C.Value ∞} →
    Stack-OK i k p s →
    Cont-OK i ⟨ c , s , comp-env ρ ⟩ k →
    [ i ] VM.stack-sizes ⟨ comp t c , s , comp-env ρ ⟩ ∼
          numbers (⟦ t ⟧⁺ ρ >>= k) (length s)

  ⟦⟧⁺-correct {p} (var x) ρ {c} {s} {k} _ c-ok =
    VM.stack-sizes ⟨ var x ∷ c , s , comp-env ρ ⟩                         ∼⟨ ∷∼∷′ ⟩

    (length s ∷′
     VM.stack-sizes ⟨ c , val (index x (comp-env ρ)) ∷ s , comp-env ρ ⟩)  ≡⟨ by (comp-index x ρ) ⟩

    (length s ∷′
     VM.stack-sizes ⟨ c , val (comp-val (index x ρ)) ∷ s , comp-env ρ ⟩)  ∼⟨ (refl ∷ λ { .force → c-ok (index x ρ) }) ⟩

    (length s ∷′ numbers (k (index x ρ)) (1 + length s))                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦ var {p = p} x ⟧⁺ ρ >>= k) (length s)                       ∎

  ⟦⟧⁺-correct {p} (ƛ t) ρ {c} {s} {k} _ c-ok =
    VM.stack-sizes ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩     ∼⟨ ∷∼∷′ ⟩

    (length s ∷′
     VM.stack-sizes ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩)  ∼⟨ (refl ∷ λ { .force → c-ok (T.ƛ t ρ) }) ⟩

    (length s ∷′ numbers (k (T.ƛ t ρ)) (1 + length s))                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦ ƛ {p = p} t ⟧⁺ ρ >>= k) (length s)                       ∎

  ⟦⟧⁺-correct {p} (t₁ · t₂) ρ {c} {s} {k} _ c-ok =
    VM.stack-sizes ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩  ∼⟨ (⟦⟧⁺-correct t₁ _ unrestricted λ v₁ →

      VM.stack-sizes ⟨ comp t₂ (app ∷ c)
                     , val (comp-val v₁) ∷ s
                     , comp-env ρ
                     ⟩                                                        ∼⟨ (⟦⟧⁺-correct t₂ _ unrestricted λ v₂ →

        VM.stack-sizes ⟨ app ∷ c
                       , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
                       , comp-env ρ
                       ⟩                                                            ∼⟨ ∙⁺-correct v₁ v₂ c-ok ⟩

        numbers ([ pred , just pred ] v₁ ∙⁺ v₂ >>= k) (2 + length s)                ∎) ⟩

      numbers (do v₂ ← ⟦ t₂ ⟧⁺ ρ
                  [ pred , just pred ] v₁ ∙⁺ v₂ >>= k)
              (1 + length s)                                                  ∎) ⟩

    numbers (do v₁ ← ⟦ t₁ ⟧⁺ ρ
                v₂ ← ⟦ t₂ ⟧⁺ ρ
                [ pred , just pred ] v₁ ∙⁺ v₂ >>= k)
            (length s)                                               ∼⟨ symmetric-∼ (numbers-cong (⟦⟧⁺-· p t₁ t₂)) ⟩

    numbers (⟦ _·_ {p = p} t₁ t₂ ⟧⁺ ρ >>= k) (length s)              ∎

  ⟦⟧⁺-correct (call f t) ρ {c} {s} {k} unrestricted c-ok =
    VM.stack-sizes ⟨ comp t (cal f ∷ c) , s , comp-env ρ ⟩                ∼⟨ (⟦⟧⁺-correct t _ unrestricted λ v →

      VM.stack-sizes ⟨ cal f ∷ c , val (comp-val v) ∷ s , comp-env ρ ⟩          ∼⟨ ∷∼∷′ ⟩

      1 + length s ∷′
      VM.stack-sizes ⟨ comp-name f
                     , ret c (comp-env ρ) ∷ s
                     , comp-val v ∷ []
                     ⟩                                                          ∼⟨ (refl ∷ λ { .force → ret-lemma (def f) [] c-ok }) ⟩

      1 + length s ∷′
      numbers (⟦ def f ⟧⁺ (v ∷ []) >>=
               Delay-crash-colist.tell pred ∘ return >>= k)
              (1 + length s)                                                    ∼⟨ symmetric-∼ ∷∼∷′ ⟩

      numbers ([ id , just pred ] T.ƛ (def f) [] ∙⁺ v >>= k)
              (1 + length s)                                                    ∎) ⟩

    numbers (⟦ t ⟧⁺ ρ >>= λ v →
             [ id , just pred ] T.ƛ (def f) [] ∙⁺ v >>= k)
            (length s)                                                    ∼⟨ numbers-cong (DCC.associativity (⟦ t ⟧⁺ _) _ _) ⟩

    numbers ((⟦ t ⟧⁺ ρ >>= [ id , just pred ] T.ƛ (def f) [] ∙⁺_) >>= k)
            (length s)                                                    ∼⟨⟩

    numbers (⟦ call f t ⟧⁺ ρ >>= k) (length s)                            ∎

  ⟦⟧⁺-correct (call f t) ρ {c} {ret c′ ρ′ ∷ s} {k}
              s-ok@(restricted-∷ c-ok) _ =
    VM.stack-sizes ⟨ comp t (tcl f ∷ c)
                   , ret c′ ρ′ ∷ s
                   , comp-env ρ
                   ⟩                                                 ∼⟨ (⟦⟧⁺-correct t _ unrestricted λ v →

      VM.stack-sizes ⟨ tcl f ∷ c
                     , val (comp-val v) ∷ ret c′ ρ′ ∷ s
                     , comp-env ρ
                     ⟩                                               ∼⟨ ∷∼∷′ ⟩

      2 + length s ∷′
      VM.stack-sizes ⟨ comp-name f
                     , ret c′ ρ′ ∷ s
                     , comp-val v ∷ []
                     ⟩                                               ∼⟨⟩

      2 + length s ∷′
      VM.stack-sizes ⟨ comp-name f
                     , ret c′ ρ′ ∷ s
                     , comp-env (v ∷ [])
                     ⟩                                               ∼⟨ (refl ∷ λ { .force → ⟦⟧⁺-correct (def f) (_ ∷ []) s-ok λ v′ →

        VM.stack-sizes ⟨ ret ∷ []
                       , val (comp-val v′) ∷ ret c′ ρ′ ∷ s
                       , comp-env (v ∷ [])
                       ⟩                                                   ∼⟨ ∷∼∷′ ⟩

        2 + length s ∷′
        VM.stack-sizes ⟨ c′ , val (comp-val v′) ∷ s , ρ′ ⟩                 ∼⟨ c-ok v′ ⟩

        numbers (k v′) (2 + length s)                                      ∎ }) ⟩

      2 + length s ∷′
      numbers (⟦ def f ⟧⁺ (v ∷ []) >>= k) (1 + length s)             ∼⟨ (refl ∷ λ { .force →
                                                                         numbers-cong (DCC.associativity (⟦ def f ⟧⁺ _) _ _) }) ⟩
      2 + length s ∷′
      numbers (⟦ def f ⟧⁺ (v ∷ []) >>= return >>= k) (1 + length s)  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

      numbers ([ pred , nothing ] T.ƛ (def f) [] ∙⁺ v >>= k)
              (2 + length s)                                         ∎) ⟩

    numbers (⟦ t ⟧⁺ ρ >>= λ v →
             [ pred , nothing ] T.ƛ (def f) [] ∙⁺ v >>= k)
            (1 + length s)                                              ∼⟨ numbers-cong (DCC.associativity (⟦ t ⟧⁺ _) _ _) ⟩

    numbers ((⟦ t ⟧⁺ ρ >>= [ pred , nothing ] T.ƛ (def f) [] ∙⁺_) >>=
             k)
            (1 + length s)                                              ∼⟨⟩

    numbers (⟦ call f t ⟧⁺ ρ >>= k) (1 + length s)                      ∎

  ⟦⟧⁺-correct {p} (con b) ρ {c} {s} {k} _ c-ok =
    VM.stack-sizes ⟨ con b ∷ c , s , comp-env ρ ⟩                       ∼⟨ ∷∼∷′ ⟩

    (length s ∷′
     VM.stack-sizes ⟨ c , val (comp-val (T.con b)) ∷ s , comp-env ρ ⟩)  ∼⟨ (refl ∷ λ { .force → c-ok (T.con b) }) ⟩

    (length s ∷′ numbers (k (T.con b)) (1 + length s))                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦ con {p = p} b ⟧⁺ ρ >>= k) (length s)                     ∎

  ⟦⟧⁺-correct (if t₁ t₂ t₃) ρ {c} {s} {k} s-ok c-ok =
    VM.stack-sizes ⟨ comp t₁ (bra (comp t₂ []) (comp t₃ []) ∷ c)
                   , s
                   , comp-env ρ
                   ⟩                                                    ∼⟨ (⟦⟧⁺-correct t₁ _ unrestricted λ v₁ → ⟦if⟧⁺-correct v₁ t₂ t₃ s-ok c-ok) ⟩

    numbers (⟦ t₁ ⟧⁺ ρ >>= λ v₁ → ⟦if⟧⁺ v₁ t₂ t₃ ρ >>= k) (length s)    ∼⟨ numbers-cong (DCC.associativity (⟦ t₁ ⟧⁺ _) _ _) ⟩

    numbers ((⟦ t₁ ⟧⁺ ρ >>= λ v₁ → ⟦if⟧⁺ v₁ t₂ t₃ ρ) >>= k) (length s)  ∎

  ret-lemma :
    ∀ {p i n n′} (t : Tm p (1 + n)) ρ {ρ′ : C.Env n′} {c s v}
      {k : T.Value → Delay-crash-colist (ℕ → ℕ) C.Value ∞} →
    Cont-OK i ⟨ c , s , ρ′ ⟩ k →
    [ i ] VM.stack-sizes ⟨ comp t (ret ∷ [])
                         , ret c ρ′ ∷ s
                         , comp-val v ∷ comp-env ρ
                         ⟩ ∼
          numbers (⟦ t ⟧⁺ (v ∷ ρ) >>=
                   Delay-crash-colist.tell pred ∘ return >>= k)
                  (1 + length s)
  ret-lemma t ρ {ρ′} {c} {s} {v} {k} c-ok =
    VM.stack-sizes ⟨ comp t (ret ∷ [])
                   , ret c ρ′ ∷ s
                   , comp-val v ∷ comp-env ρ
                   ⟩                                           ∼⟨⟩

    VM.stack-sizes ⟨ comp t (ret ∷ [])
                   , ret c ρ′ ∷ s
                   , comp-env (v ∷ ρ)
                   ⟩                                           ∼⟨ (⟦⟧⁺-correct t (_ ∷ _) (ret-ok c-ok) λ v′ →

      VM.stack-sizes ⟨ ret ∷ []
                     , val (comp-val v′) ∷ ret c ρ′ ∷ s
                     , comp-env (v ∷ ρ)
                     ⟩                                               ∼⟨ ∷∼∷′ ⟩

      2 + length s ∷′
      VM.stack-sizes ⟨ c , val (comp-val v′) ∷ s , ρ′ ⟩              ∼⟨ (refl ∷ λ { .force → c-ok v′ }) ⟩

      2 + length s ∷′ numbers (k v′) (1 + length s)                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

      numbers (tell pred (k v′)) (2 + length s)                      ∎) ⟩

    numbers (⟦ t ⟧⁺ (v ∷ ρ) >>= tell pred ∘ k) (1 + length s)  ∼⟨ numbers-cong (DCC.associativity (⟦ t ⟧⁺ _) _ _) ⟩

    numbers (⟦ t ⟧⁺ (v ∷ ρ) >>=
             Delay-crash-colist.tell pred ∘ return >>= k)
            (1 + length s)                                     ∎

  ∙⁺-correct :
    ∀ {i n} v₁ v₂ {ρ : C.Env n} {c s}
      {k : T.Value → Delay-crash-colist (ℕ → ℕ) C.Value ∞} →
    Cont-OK i ⟨ c , s , ρ ⟩ k →
    [ i ] VM.stack-sizes ⟨ app ∷ c
                         , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
                         , ρ
                         ⟩ ∼
          numbers ([ pred , just pred ] v₁ ∙⁺ v₂ >>= k) (2 + length s)

  ∙⁺-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} c-ok =
    VM.stack-sizes ⟨ app ∷ c
                   , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
                   , ρ
                   ⟩                                                     ∼⟨ ∷∼∷′ ⟩

    2 + length s ∷′
    VM.stack-sizes ⟨ comp t₁ (ret ∷ [])
                   , ret c ρ ∷ s
                   , comp-val v₂ ∷ comp-env ρ₁
                   ⟩                                                     ∼⟨ (refl ∷ λ { .force → ret-lemma t₁ _ c-ok }) ⟩

    2 + length s ∷′
    numbers (⟦ t₁ ⟧⁺ (v₂ ∷ ρ₁) >>=
             Delay-crash-colist.tell pred ∘ return >>= k)
            (1 + length s)                                               ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers ([ pred , just pred ] T.ƛ t₁ ρ₁ ∙⁺ v₂ >>= k) (2 + length s)  ∎

  ∙⁺-correct (T.con b) v₂ {ρ} {c} {s} {k} _ =
    VM.stack-sizes ⟨ app ∷ c
                   , val (comp-val v₂) ∷ val (C.con b) ∷ s
                   , ρ
                   ⟩                                                   ∼⟨ ∷∼∷′ ⟩

    2 + length s ∷′ []                                                 ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers ([ pred , just pred ] T.con b ∙⁺ v₂ >>= k) (2 + length s)  ∎

  ⟦if⟧⁺-correct :
    ∀ {p i n} v₁ t₂ t₃ {ρ : T.Env n} {c s}
      {k : T.Value → Delay-crash-colist (ℕ → ℕ) C.Value ∞} →
    Stack-OK i k p s →
    Cont-OK i ⟨ c , s , comp-env ρ ⟩ k →
    [ i ] VM.stack-sizes ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
                         , val (comp-val v₁) ∷ s
                         , comp-env ρ
                         ⟩ ∼
          numbers (⟦if⟧⁺ v₁ t₂ t₃ ρ >>= k) (1 + length s)

  ⟦if⟧⁺-correct (T.ƛ t₁ ρ₁) t₂ t₃ {ρ} {c} {s} {k} _ _ =
    VM.stack-sizes ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
                   , val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
                   , comp-env ρ
                   ⟩                                          ∼⟨ ∷∼∷′ ⟩

    1 + length s ∷′ []                                        ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦if⟧⁺ (T.ƛ t₁ ρ₁) t₂ t₃ ρ >>= k) (1 + length s)  ∎

  ⟦if⟧⁺-correct (T.con true) t₂ t₃ {ρ} {c} {s} {k} s-ok c-ok =
    VM.stack-sizes ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
                   , val (comp-val (T.con true)) ∷ s
                   , comp-env ρ
                   ⟩                                           ∼⟨ ∷∼∷′ ⟩

    1 + length s ∷′
    VM.stack-sizes ⟨ comp t₂ [] ++ c , s , comp-env ρ ⟩        ≡⟨ by (comp-++ t₂) ⟩

    1 + length s ∷′
    VM.stack-sizes ⟨ comp t₂ c , s , comp-env ρ ⟩              ∼⟨ (refl ∷ λ { .force → ⟦⟧⁺-correct t₂ _ s-ok c-ok }) ⟩

    1 + length s ∷′ numbers (⟦ t₂ ⟧⁺ ρ >>= k) (length s)       ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦if⟧⁺ (T.con true) t₂ t₃ ρ >>= k) (1 + length s)  ∎

  ⟦if⟧⁺-correct (T.con false) t₂ t₃ {ρ} {c} {s} {k} s-ok c-ok =
    VM.stack-sizes ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
                   , val (comp-val (T.con false)) ∷ s
                   , comp-env ρ
                   ⟩                                            ∼⟨ ∷∼∷′ ⟩

    1 + length s ∷′
    VM.stack-sizes ⟨ comp t₃ [] ++ c , s , comp-env ρ ⟩         ≡⟨ by (comp-++ t₃) ⟩

    1 + length s ∷′
    VM.stack-sizes ⟨ comp t₃ c , s , comp-env ρ ⟩               ∼⟨ (refl ∷ λ { .force → ⟦⟧⁺-correct t₃ _ s-ok c-ok }) ⟩

    1 + length s ∷′ numbers (⟦ t₃ ⟧⁺ ρ >>= k) (length s)        ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦if⟧⁺ (T.con false) t₂ t₃ ρ >>= k) (1 + length s)  ∎

-- The virtual machine and the interpreter produce bisimilar lists of
-- stack sizes.
--
-- Note that this lemma only applies to expressions without tail
-- calls. However, such expressions are allowed to contain calls to
-- definitions which do make use of tail calls.

stack-sizes-match :
  (t : Tm false 0) →
  [ ∞ ] VM.stack-sizes ⟨ comp t [] , [] , [] ⟩ ∼ I.stack-sizes t
stack-sizes-match t =
  VM.stack-sizes ⟨ comp t [] , [] , [] ⟩  ∼⟨ ⟦⟧⁺-correct t [] unrestricted (λ _ → refl ∷ λ { .force → reflexive-∼ _ }) ⟩
  numbers (comp-val ⟨$⟩ ⟦ t ⟧⁺ []) 0      ∼⟨ scanl-cong (DCC.colist-⟨$⟩ _) ⟩
  numbers (⟦ t ⟧⁺ []) 0                   ∼⟨⟩
  I.stack-sizes t                         ∎

-- The maximum stack sizes match.
--
-- Note that this lemma only applies to expressions without tail
-- calls. However, such expressions are allowed to contain calls to
-- definitions which do make use of tail calls.

maximum-stack-sizes-match :
  ∀ (t : Tm false 0) {i v} →
  Least-upper-bound (I.stack-sizes t) i →
  Least-upper-bound (VM.stack-sizes ⟨ comp t [] , [] , [] ⟩) v →
  Conat.[ ∞ ] i ∼ v
maximum-stack-sizes-match t {i} {v} i-lub =
  Least-upper-bound (VM.stack-sizes ⟨ comp t [] , [] , [] ⟩) v  ↝⟨ Least-upper-bound-∼ (stack-sizes-match t) (Conat.reflexive-∼ _) ⟩
  Least-upper-bound (I.stack-sizes t) v                         ↝⟨ lub-unique i-lub ⟩□
  Conat.[ ∞ ] i ∼ v                                             □
