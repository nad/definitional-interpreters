------------------------------------------------------------------------
-- A counterexample: The number of steps taken by the uninstrumented
-- interpreter is not, in general, linear in the number of steps taken
-- by the virtual machine for the corresponding compiled program
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Prelude

import Lambda.Syntax

module Lambda.Interpreter.Steps.Counterexample
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm 1)
  where

open import Conat
  hiding ([_]_∼_; step-∼) renaming (_+_ to _⊕_; _*_ to _⊛_)
import Equality.Propositional as E
open import Prelude.Size

open import Monad E.equality-with-J hiding (_⊛_)
import Nat E.equality-with-J as Nat
open import Vec.Data E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity

open import Lambda.Delay-crash
open import Lambda.Interpreter def
open import Lambda.Compiler def
open import Lambda.Virtual-machine comp-name
open import Lambda.Virtual-machine.Instructions Name hiding (crash)

open Closure Tm

-- The uninstrumented interpreter does not provide a suitable cost
-- measure, in the sense that there is a family of programs for which
-- the running "time" (number of steps) of the corresponding compiled
-- programs on the virtual machine is not linear in the running time
-- on the interpreter.

not-suitable-cost-measure :
  ∃ λ (t : ℕ → Tm 0) →
    ¬ ∃ λ k₁ → ∃ λ k₂ → ∀ n →
      [ ∞ ] steps (exec ⟨ comp₀ (t n) , [] , [] ⟩) ≤
            ⌜ k₁ ⌝ ⊕ ⌜ k₂ ⌝ ⊛ steps (⟦ t n ⟧ [])
not-suitable-cost-measure =
  t , λ { (k₁ , k₂ , hyp) → Nat.+≮ 2 $ ⌜⌝-mono⁻¹ (
    ⌜ 3 + k₁ ⌝                               ∼⟨ symmetric-∼ (steps-exec-t∼ k₁) ⟩≤
    steps (exec ⟨ comp₀ (t k₁) , [] , [] ⟩)  ≤⟨ hyp k₁ ⟩
    ⌜ k₁ ⌝ ⊕ ⌜ k₂ ⌝ ⊛ steps (⟦ t k₁ ⟧ [])    ∼⟨ (⌜ k₁ ⌝ ∎∼) +-cong (_ ∎∼) *-cong steps⟦t⟧∼0 k₁ ⟩≤
    ⌜ k₁ ⌝ ⊕ ⌜ k₂ ⌝ ⊛ zero                   ∼⟨ (_ ∎∼) +-cong *-right-zero ⟩≤
    ⌜ k₁ ⌝ ⊕ zero                            ∼⟨ +-right-identity _ ⟩≤
    ⌜ k₁ ⌝                                   ∎≤) }
  where
  -- A family of programs.

  t : ℕ → Tm 0
  t zero    = con true · con true
  t (suc n) = con true · t n

  -- The semantics of every program in this family is strongly
  -- bisimilar to crash.

  ⟦t⟧∼crash : ∀ {i} n → [ i ] ⟦ t n ⟧ [] ∼ crash
  ⟦t⟧∼crash zero    = crash  ∎
  ⟦t⟧∼crash (suc n) =
    ⟦ t (suc n) ⟧ []            ∼⟨⟩
    ⟦ t n ⟧ [] >>= con true ∙_  ∼⟨ ⟦t⟧∼crash n >>=-cong (λ _ → _ ∎) ⟩
    crash >>= con true ∙_       ∼⟨⟩
    crash                       ∎

  -- Thus these programs all terminate (unsuccessfully) in zero steps.

  steps⟦t⟧∼0 : ∀ {i} n → Conat.[ i ] steps (⟦ t n ⟧ []) ∼ zero
  steps⟦t⟧∼0 = steps-cong ∘ ⟦t⟧∼crash

  -- However, running the compiled program corresponding to t n on the
  -- virtual machine takes 3 + n steps.

  steps-exec-t∼ :
    ∀ {i} n →
    Conat.[ i ] steps (exec ⟨ comp₀ (t n) , [] , [] ⟩) ∼ ⌜ 3 + n ⌝
  steps-exec-t∼ = lemma
    where
    lemma :
      ∀ {i c s} n →
      Conat.[ i ] steps (exec ⟨ comp false (t n) c , s , [] ⟩) ∼
                  ⌜ 3 + n ⌝
    lemma zero    = suc λ { .force →
                    suc λ { .force →
                    suc λ { .force →
                    zero }}}
    lemma (suc n) = suc λ { .force → lemma n }
