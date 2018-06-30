------------------------------------------------------------------------
-- The actual maximum stack size of the compiled program matches the
-- maximum stack size of the annotated source-level semantics
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

import Lambda.Syntax

module Lambda.Compiler-correctness.Sizes-match
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm 1)
  where

open import Colist hiding (_++_)
import Conat
open import Equality.Propositional as E using (refl)
open import Prelude
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
  module C = Closure Code
  module T = Closure Tm

------------------------------------------------------------------------
-- A lemma

-- A rearrangement lemma for ⟦_⟧⁺.

⟦⟧⁺-· :
  ∀ {A n} (t₁ t₂ : Tm n)
    {ρ} {k : T.Value → Delay-crash-colist (ℕ → ℕ) A ∞} →
  DCC.[ ∞ ] ⟦ t₁ · t₂ ⟧⁺ ρ >>= k ∼
            do v₁ ← ⟦ t₁ ⟧⁺ ρ
               v₂ ← ⟦ t₂ ⟧⁺ ρ
               [ pred ] v₁ ∙⁺ v₂ >>= k
⟦⟧⁺-· t₁ t₂ {ρ} {k} =
  ⟦ t₁ · t₂ ⟧⁺ ρ >>= k               DCC.∼⟨⟩

  (do v₁ ← ⟦ t₁ ⟧⁺ ρ
      v₂ ← ⟦ t₂ ⟧⁺ ρ
      [ pred ] v₁ ∙⁺ v₂) >>= k       DCC.∼⟨ DCC.symmetric (DCC.associativity (⟦ t₁ ⟧⁺ _) _ _) ⟩

  (do v₁ ← ⟦ t₁ ⟧⁺ ρ
      (do v₂ ← ⟦ t₂ ⟧⁺ ρ
          [ pred ] v₁ ∙⁺ v₂) >>= k)  DCC.∼⟨ ((⟦ t₁ ⟧⁺ _ DCC.∎) DCC.>>=-cong λ _ → DCC.symmetric (DCC.associativity (⟦ t₂ ⟧⁺ _) _ _)) ⟩

  (do v₁ ← ⟦ t₁ ⟧⁺ ρ
      v₂ ← ⟦ t₂ ⟧⁺ ρ
      [ pred ] v₁ ∙⁺ v₂ >>= k)       DCC.∎

------------------------------------------------------------------------
-- The stack sizes match

mutual

  -- Some lemmas.

  ⟦⟧⁺-correct :
    ∀ {i n} t (ρ : T.Env n) {c s}
      {k : T.Value → Delay-crash-colist (ℕ → ℕ) C.Value ∞} →
    (∀ v →
       [ i ] VM.stack-sizes ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ∼
             numbers (k v) (1 + length s)) →
    [ i ] VM.stack-sizes ⟨ comp t c , s , comp-env ρ ⟩ ∼
          numbers (⟦ t ⟧⁺ ρ >>= k) (length s)

  ⟦⟧⁺-correct (var x) ρ {c} {s} {k} hyp =
    VM.stack-sizes ⟨ var x ∷ c , s , comp-env ρ ⟩                         ∼⟨ ∷∼∷′ ⟩

    (length s ∷′
     VM.stack-sizes ⟨ c , val (index x (comp-env ρ)) ∷ s , comp-env ρ ⟩)  ≡⟨ by (comp-index x ρ) ⟩

    (length s ∷′
     VM.stack-sizes ⟨ c , val (comp-val (index x ρ)) ∷ s , comp-env ρ ⟩)  ∼⟨ (refl ∷ λ { .force → hyp (index x ρ) }) ⟩

    (length s ∷′ numbers (k (index x ρ)) (1 + length s))                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦ var x ⟧⁺ ρ >>= k) (length s)                               ∎

  ⟦⟧⁺-correct (ƛ t) ρ {c} {s} {k} hyp =
    VM.stack-sizes ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩     ∼⟨ ∷∼∷′ ⟩

    (length s ∷′
     VM.stack-sizes ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩)  ∼⟨ (refl ∷ λ { .force → hyp (T.ƛ t ρ) }) ⟩

    (length s ∷′ numbers (k (T.ƛ t ρ)) (1 + length s))                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦ ƛ t ⟧⁺ ρ >>= k) (length s)                               ∎

  ⟦⟧⁺-correct (t₁ · t₂) ρ {c} {s} {k} hyp =
    VM.stack-sizes ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩  ∼⟨ (⟦⟧⁺-correct t₁ _ λ v₁ → ⟦⟧⁺-correct t₂ _ λ v₂ → ∙⁺-correct v₁ v₂ hyp) ⟩

    numbers (do v₁ ← ⟦ t₁ ⟧⁺ ρ
                v₂ ← ⟦ t₂ ⟧⁺ ρ
                [ pred ] v₁ ∙⁺ v₂ >>= k)
            (length s)                                               ∼⟨ symmetric-∼ (numbers-cong (⟦⟧⁺-· t₁ t₂)) ⟩

    numbers (⟦ t₁ · t₂ ⟧⁺ ρ >>= k) (length s)                        ∎

  ⟦⟧⁺-correct (call f t) ρ {c} {s} {k} hyp =
    VM.stack-sizes ⟨ comp t (cal f ∷ c) , s , comp-env ρ ⟩               ∼⟨ (⟦⟧⁺-correct t _ λ v →

      VM.stack-sizes ⟨ cal f ∷ c , val (comp-val v) ∷ s , comp-env ρ ⟩         ∼⟨ ∷∼∷′ ⟩

      1 + length s ∷′
      VM.stack-sizes ⟨ comp-name f
                     , ret c (comp-env ρ) ∷ s
                     , comp-val v ∷ []
                     ⟩                                                         ∼⟨⟩

      1 + length s ∷′
      VM.stack-sizes ⟨ comp-name f
                     , ret c (comp-env ρ) ∷ s
                     , comp-env (v ∷ [])
                     ⟩                                                         ∼⟨ (refl ∷ λ { .force → ⟦⟧⁺-correct (def f) (_ ∷ []) λ v′ →

        VM.stack-sizes ⟨ ret ∷ []
                       , val (comp-val v′) ∷ ret c (comp-env ρ) ∷ s
                       , comp-env (v ∷ [])
                       ⟩                                                             ∼⟨ ∷∼∷′ ⟩

        2 + length s ∷′
        VM.stack-sizes ⟨ c , val (comp-val v′) ∷ s , comp-env ρ ⟩                    ∼⟨ (refl ∷ λ { .force → hyp v′ }) ⟩

        2 + length s ∷′ numbers (k v′) (1 + length s)                                ∼⟨ symmetric-∼ ∷∼∷′ ⟩

        numbers (tell pred (k v′)) (2 + length s)                                    ∎ }) ⟩

      1 + length s ∷′
      numbers (⟦ def f ⟧⁺ (v ∷ []) >>= λ v →
               Delay-crash-colist.tell pred (return v) >>= k)
              (1 + length s)                                                   ∼⟨ (refl ∷ λ { .force →
                                                                                   numbers-cong (DCC.associativity (⟦ def f ⟧⁺ _) _ _) }) ⟩
      1 + length s ∷′
      numbers (⟦ def f ⟧⁺ (v ∷ []) >>=
               Delay-crash-colist.tell pred ∘ return >>= k)
              (1 + length s)                                                   ∼⟨ symmetric-∼ ∷∼∷′ ⟩

      numbers ([ id ] T.ƛ (def f) [] ∙⁺ v >>= k) (1 + length s)                ∎) ⟩

    numbers (⟦ t ⟧⁺ ρ >>= λ v → [ id ] T.ƛ (def f) [] ∙⁺ v >>= k)
            (length s)                                                   ∼⟨ numbers-cong (DCC.associativity (⟦ t ⟧⁺ _) _ _) ⟩

    numbers ((⟦ t ⟧⁺ ρ >>= [ id ] T.ƛ (def f) [] ∙⁺_) >>= k) (length s)  ∼⟨⟩

    numbers (⟦ call f t ⟧⁺ ρ >>= k) (length s)                           ∎

  ⟦⟧⁺-correct (con b) ρ {c} {s} {k} hyp =
    VM.stack-sizes ⟨ con b ∷ c , s , comp-env ρ ⟩                       ∼⟨ ∷∼∷′ ⟩

    (length s ∷′
     VM.stack-sizes ⟨ c , val (comp-val (T.con b)) ∷ s , comp-env ρ ⟩)  ∼⟨ (refl ∷ λ { .force → hyp (T.con b) }) ⟩

    (length s ∷′ numbers (k (T.con b)) (1 + length s))                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦ con b ⟧⁺ ρ >>= k) (length s)                             ∎

  ⟦⟧⁺-correct (if t₁ t₂ t₃) ρ {c} {s} {k} hyp =
    VM.stack-sizes ⟨ comp t₁ (bra (comp t₂ []) (comp t₃ []) ∷ c)
                   , s
                   , comp-env ρ
                   ⟩                                                    ∼⟨ (⟦⟧⁺-correct t₁ _ λ v₁ → ⟦if⟧⁺-correct v₁ t₂ t₃ hyp) ⟩

    numbers (⟦ t₁ ⟧⁺ ρ >>= λ v₁ → ⟦if⟧⁺ v₁ t₂ t₃ ρ >>= k) (length s)    ∼⟨ numbers-cong (DCC.associativity (⟦ t₁ ⟧⁺ _) _ _) ⟩

    numbers ((⟦ t₁ ⟧⁺ ρ >>= λ v₁ → ⟦if⟧⁺ v₁ t₂ t₃ ρ) >>= k) (length s)  ∎

  ∙⁺-correct :
    ∀ {i n} v₁ v₂ {ρ : T.Env n} {c s}
      {k : T.Value → Delay-crash-colist (ℕ → ℕ) C.Value ∞} →
    (∀ v →
       [ i ] VM.stack-sizes ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ∼
             numbers (k v) (1 + length s)) →
    [ i ] VM.stack-sizes ⟨ app ∷ c
                         , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
                         , comp-env ρ
                         ⟩ ∼
          numbers ([ pred ] v₁ ∙⁺ v₂ >>= k) (2 + length s)

  ∙⁺-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} hyp =
    VM.stack-sizes ⟨ app ∷ c
                   , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
                   , comp-env ρ
                   ⟩                                                     ∼⟨ ∷∼∷′ ⟩

    2 + length s ∷′
    VM.stack-sizes ⟨ comp t₁ (ret ∷ [])
                   , ret c (comp-env ρ) ∷ s
                   , comp-val v₂ ∷ comp-env ρ₁
                   ⟩                                                     ∼⟨ (refl ∷ λ { .force →

      VM.stack-sizes ⟨ comp t₁ (ret ∷ [])
                    , ret c (comp-env ρ) ∷ s
                    , comp-val v₂ ∷ comp-env ρ₁
                    ⟩                                                          ∼⟨⟩

      VM.stack-sizes ⟨ comp t₁ (ret ∷ [])
                     , ret c (comp-env ρ) ∷ s
                     , comp-env (v₂ ∷ ρ₁)
                     ⟩                                                         ∼⟨ ⟦⟧⁺-correct t₁ (_ ∷ _) (λ v →

        VM.stack-sizes ⟨ ret ∷ []
                       , val (comp-val v) ∷ ret c (comp-env ρ) ∷ s
                       , comp-env (v₂ ∷ ρ₁)
                       ⟩                                                            ∼⟨ ∷∼∷′ ⟩

        2 + length s ∷′
        VM.stack-sizes ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩                    ∼⟨ (refl ∷ λ { .force → hyp v }) ⟩

        2 + length s ∷′ numbers (k v) (1 + length s)                                ∼⟨ symmetric-∼ ∷∼∷′ ⟩

        numbers (tell pred (k v)) (2 + length s)                                    ∎) ⟩

      numbers (⟦ t₁ ⟧⁺ (v₂ ∷ ρ₁) >>= tell pred ∘ k) (1 + length s)             ∎ }) ⟩

    2 + length s ∷′
    numbers (⟦ t₁ ⟧⁺ (v₂ ∷ ρ₁) >>= tell pred ∘ k) (1 + length s)         ∼⟨⟩

    2 + length s ∷′
    numbers (⟦ t₁ ⟧⁺ (v₂ ∷ ρ₁) >>= λ v → tell pred (return v) >>= k)
            (1 + length s)                                               ∼⟨ (refl ∷ λ { .force →
                                                                             numbers-cong (DCC.associativity (⟦ t₁ ⟧⁺ _) _ _) }) ⟩
    2 + length s ∷′
    numbers (⟦ t₁ ⟧⁺ (v₂ ∷ ρ₁) >>=
             Delay-crash-colist.tell pred ∘ return >>= k)
            (1 + length s)                                               ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers ([ pred ] T.ƛ t₁ ρ₁ ∙⁺ v₂ >>= k) (2 + length s)              ∎

  ∙⁺-correct (T.con b) v₂ {ρ} {c} {s} {k} hyp =
    VM.stack-sizes ⟨ app ∷ c
                   , val (comp-val v₂) ∷ val (C.con b) ∷ s
                   , comp-env ρ
                   ⟩                                        ∼⟨ ∷∼∷′ ⟩

    2 + length s ∷′ []                                      ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers ([ pred ] T.con b ∙⁺ v₂ >>= k) (2 + length s)   ∎

  ⟦if⟧⁺-correct :
    ∀ {i n} v₁ t₂ t₃ {ρ : T.Env n} {c s}
      {k : T.Value → Delay-crash-colist (ℕ → ℕ) C.Value ∞} →
    (∀ v →
       [ i ] VM.stack-sizes ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ∼
             numbers (k v) (1 + length s)) →
    [ i ] VM.stack-sizes ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
                         , val (comp-val v₁) ∷ s
                         , comp-env ρ
                         ⟩ ∼
          numbers (⟦if⟧⁺ v₁ t₂ t₃ ρ >>= k) (1 + length s)

  ⟦if⟧⁺-correct (T.ƛ t₁ ρ₁) t₂ t₃ {ρ} {c} {s} {k} hyp =
    VM.stack-sizes ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
                   , val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
                   , comp-env ρ
                   ⟩                                          ∼⟨ ∷∼∷′ ⟩

    1 + length s ∷′ []                                        ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦if⟧⁺ (T.ƛ t₁ ρ₁) t₂ t₃ ρ >>= k) (1 + length s)  ∎

  ⟦if⟧⁺-correct (T.con true) t₂ t₃ {ρ} {c} {s} {k} hyp =
    VM.stack-sizes ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
                   , val (comp-val (T.con true)) ∷ s
                   , comp-env ρ
                   ⟩                                           ∼⟨ ∷∼∷′ ⟩

    1 + length s ∷′
    VM.stack-sizes ⟨ comp t₂ [] ++ c , s , comp-env ρ ⟩        ≡⟨ by (comp-++ t₂) ⟩

    1 + length s ∷′
    VM.stack-sizes ⟨ comp t₂ c , s , comp-env ρ ⟩              ∼⟨ (refl ∷ λ { .force → ⟦⟧⁺-correct t₂ _ hyp }) ⟩

    1 + length s ∷′ numbers (⟦ t₂ ⟧⁺ ρ >>= k) (length s)       ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦if⟧⁺ (T.con true) t₂ t₃ ρ >>= k) (1 + length s)  ∎

  ⟦if⟧⁺-correct (T.con false) t₂ t₃ {ρ} {c} {s} {k} hyp =
    VM.stack-sizes ⟨ bra (comp t₂ []) (comp t₃ []) ∷ c
                   , val (comp-val (T.con false)) ∷ s
                   , comp-env ρ
                   ⟩                                            ∼⟨ ∷∼∷′ ⟩

    1 + length s ∷′
    VM.stack-sizes ⟨ comp t₃ [] ++ c , s , comp-env ρ ⟩         ≡⟨ by (comp-++ t₃) ⟩

    1 + length s ∷′
    VM.stack-sizes ⟨ comp t₃ c , s , comp-env ρ ⟩               ∼⟨ (refl ∷ λ { .force → ⟦⟧⁺-correct t₃ _ hyp }) ⟩

    1 + length s ∷′ numbers (⟦ t₃ ⟧⁺ ρ >>= k) (length s)        ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦if⟧⁺ (T.con false) t₂ t₃ ρ >>= k) (1 + length s)  ∎

-- The virtual machine and the interpreter produce bisimilar lists of
-- stack sizes.

stack-sizes-match :
  ∀ t →
  [ ∞ ] VM.stack-sizes ⟨ comp t [] , [] , [] ⟩ ∼ I.stack-sizes t []
stack-sizes-match t =
  VM.stack-sizes ⟨ comp t [] , [] , [] ⟩  ∼⟨ ⟦⟧⁺-correct t [] (λ _ → refl ∷ λ { .force → reflexive-∼ _ }) ⟩
  numbers (comp-val ⟨$⟩ ⟦ t ⟧⁺ []) 0      ∼⟨ scanl-cong (DCC.colist-⟨$⟩ _) ⟩
  numbers (⟦ t ⟧⁺ []) 0                   ∼⟨⟩
  I.stack-sizes t []                      ∎

-- The maximum stack sizes match.

maximum-stack-sizes-match :
  ∀ t {i v} →
  Least-upper-bound (I.stack-sizes t []) i →
  Least-upper-bound (VM.stack-sizes ⟨ comp t [] , [] , [] ⟩) v →
  Conat.[ ∞ ] i ∼ v
maximum-stack-sizes-match t {i} {v} i-lub =
  Least-upper-bound (VM.stack-sizes ⟨ comp t [] , [] , [] ⟩) v  ↝⟨ Least-upper-bound-∼ (stack-sizes-match t) (Conat.reflexive-∼ _) ⟩
  Least-upper-bound (I.stack-sizes t []) v                      ↝⟨ lub-unique i-lub ⟩□
  Conat.[ ∞ ] i ∼ v                                             □
