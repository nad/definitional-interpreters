------------------------------------------------------------------------
-- The actual maximum stack size of the compiled program matches the
-- maximum stack size of the annotated source-level semantics
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Compiler-correctness.Sizes-match where

open import Colist
import Conat
open import Equality.Propositional as E using (refl)
open import Prelude
open import Tactic.By using (by)

open import Function-universe E.equality-with-J hiding (_∘_)
open import List E.equality-with-J using (length)
open import Monad E.equality-with-J
open import Nat E.equality-with-J
open import Vec.Data E.equality-with-J

open import Upper-bounds

open import Lambda.Compiler
open import Lambda.Interpreter.Annotated as I
open import Lambda.Delay-crash-colist as DCC
  using (Delay-crash-colist; tell)
open import Lambda.Syntax
open import Lambda.Virtual-machine as VM

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
               v₁ ∙⁺ v₂ >>= k
⟦⟧⁺-· t₁ t₂ {ρ} {k} =
  ⟦ t₁ · t₂ ⟧⁺ ρ >>= k      DCC.∼⟨⟩

  (do v₁ ← ⟦ t₁ ⟧⁺ ρ
      v₂ ← ⟦ t₂ ⟧⁺ ρ
      v₁ ∙⁺ v₂) >>= k       DCC.∼⟨ DCC.symmetric (DCC.associativity (⟦ t₁ ⟧⁺ _) _ _) ⟩

  (do v₁ ← ⟦ t₁ ⟧⁺ ρ
      (do v₂ ← ⟦ t₂ ⟧⁺ ρ
          v₁ ∙⁺ v₂) >>= k)  DCC.∼⟨ ((⟦ t₁ ⟧⁺ _ DCC.∎) DCC.>>=-cong λ _ → DCC.symmetric (DCC.associativity (⟦ t₂ ⟧⁺ _) _ _)) ⟩

  (do v₁ ← ⟦ t₁ ⟧⁺ ρ
      v₂ ← ⟦ t₂ ⟧⁺ ρ
      v₁ ∙⁺ v₂ >>= k)       DCC.∎

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

  ⟦⟧⁺-correct (con i) ρ {c} {s} {k} hyp =
    VM.stack-sizes ⟨ con i ∷ c , s , comp-env ρ ⟩                       ∼⟨ ∷∼∷′ ⟩

    (length s ∷′
     VM.stack-sizes ⟨ c , val (comp-val (T.con i)) ∷ s , comp-env ρ ⟩)  ∼⟨ (refl ∷ λ { .force → hyp (T.con i) }) ⟩

    (length s ∷′ numbers (k (T.con i)) (1 + length s))                  ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (⟦ con i ⟧⁺ ρ >>= k) (length s)                             ∎

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
                v₁ ∙⁺ v₂ >>= k)
            (length s)                                               ∼⟨ symmetric-∼ (numbers-cong (⟦⟧⁺-· t₁ t₂)) ⟩

    numbers (⟦ t₁ · t₂ ⟧⁺ ρ >>= k) (length s)                        ∎

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
          numbers (v₁ ∙⁺ v₂ >>= k) (2 + length s)

  ∙⁺-correct (T.con i) v₂ {ρ} {c} {s} {k} hyp =
    VM.stack-sizes ⟨ app ∷ c
                   , val (comp-val v₂) ∷ val (C.con i) ∷ s
                   , comp-env ρ
                   ⟩                                        ∼⟨ ∷∼∷′ ⟩

    2 + length s ∷′ []                                      ∼⟨ symmetric-∼ ∷∼∷′ ⟩

    numbers (T.con i ∙⁺ v₂ >>= k) (2 + length s)            ∎

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

    numbers (T.ƛ t₁ ρ₁ ∙⁺ v₂ >>= k) (2 + length s)                       ∎

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
