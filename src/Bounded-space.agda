------------------------------------------------------------------------
-- Definitional interpreters can model systems with bounded space
------------------------------------------------------------------------

-- In "Reasoning on Divergent Computations with Coaxioms" Ancona,
-- Dagnino and Zucca write the following:
--
--   "To assess the applicability and generality of our approach much
--   work is still needed. We are currently considering to apply
--   coaxioms to other kinds of semantics; in particular, trace
--   semantics seems particularly interesting for investigating
--   whether our approach is suitable for formalizing and proving
--   important safety properties of non terminating programs, as
--   ensuring that a server will never try to use infinite resources.
--   Other approaches based on definitional interpreters [Danielsson
--   2012], and the adoption of step counters [Amin and Rompf 2017;
--   Ancona 2014; Ernst et al. 2006; Owens et al. 2016] seem to be
--   appealing for proving type soundness properties with big-step
--   semantics, and other results concerning program equivalence;
--   however, it is not clear whether these solutions work well for
--   other kinds of properties. For instance, if a program consists of
--   an infinite loop that allocates new heap space at each step
--   without releasing it, one would like to conclude that it will
--   eventually crash even though a definitional interpreter returns
--   timeout for all possible values of the step counter."
--
-- This is an attempt to show that definitional interpreters can
-- handle this situation.

{-# OPTIONS --without-K --safe #-}

module Bounded-space where

open import Colist
open import Delay-monad
open import Delay-monad.Weak-bisimilarity as W
  hiding (reflexive; symmetric; transitive)
open import Equality.Propositional
open import Prelude
open import Tactic.By

open import Nat equality-with-J

------------------------------------------------------------------------
-- Programs

-- Statements.

data Stmt : Set where
  allocate deallocate : Stmt

-- Programs are potentially infinite sequences of statements.

Program : Size → Set
Program i = Colist Stmt i

------------------------------------------------------------------------
-- Heaps

-- Heaps. (Only a size. The natural number is wrapped, to avoid
-- confusing heaps and size limits.)

record Heap : Set where
  field
    size : ℕ

open Heap public

-- An empty heap.

empty : Heap
empty = record { size = 0 }

-- Increases the heap's size by one.

grow : Heap → Heap
grow h = record h { size = suc (size h) }

-- Reduces the heap's size by one, if possible.

shrink : Heap → Heap
shrink h = record h { size = pred (size h) }

------------------------------------------------------------------------
-- Definitional interpreter

-- One step of computation.

step : Stmt → Heap → ℕ → Maybe Heap
step deallocate heap limit = just (shrink heap)
                             -- Does not crash for empty heaps.
step allocate   heap limit =
  if size heap ≟ limit       -- Crashes if the heap already has
    then nothing             -- the maximum size.
    else just (grow heap)

-- A definitional interpreter. The natural number is the maximum size
-- of the heap.

⟦_⟧ : ∀ {i} → Program ∞ → Heap → ℕ → Delay (Maybe Heap) i
⟦ []    ⟧ heap limit = now (just heap)
⟦ s ∷ p ⟧ heap limit =
  case step s heap limit of λ where
    nothing     → now nothing
    (just heap) → later λ { .force → ⟦ force p ⟧ heap limit }

------------------------------------------------------------------------
-- A program equivalence

-- An equivalence relation that identifies programs that, given a
-- sufficient amount of memory, behave identically (up to weak
-- bisimilarity, when the initial heap is empty).

infix 4 _≘_

_≘_ : Program ∞ → Program ∞ → Set
p ≘ q =
  ∃ λ bound → ∀ l →
  ⟦ p ⟧ empty (bound + l) ≈ ⟦ q ⟧ empty (bound + l)

-- The relation is an equivalence relation.

reflexive : ∀ {p} → p ≘ p
reflexive = 0 , λ _ → W.reflexive _

symmetric : ∀ {p q} → p ≘ q → q ≘ p
symmetric = Σ-map id (W.symmetric ∘_)

transitive : ∀ {p q r} → p ≘ q → q ≘ r → p ≘ r
transitive {p} {q} {r} (b₁ , p₁) (b₂ , p₂) =
  max b₁ b₂ , λ l →
    ⟦ p ⟧ empty (max b₁ b₂ + l)         ≡⟨ by (lemma₀ b₁) ⟩≈
    ⟦ p ⟧ empty (b₁ + ((b₂ ∸ b₁) + l))  ≈⟨ p₁ ((b₂ ∸ b₁) + l) ⟩
    ⟦ q ⟧ empty (b₁ + ((b₂ ∸ b₁) + l))  ≡⟨ by lemma₃ ⟩≈
    ⟦ q ⟧ empty (b₂ + ((b₁ ∸ b₂) + l))  ≈⟨ p₂ ((b₁ ∸ b₂) + l) ⟩
    ⟦ r ⟧ empty (b₂ + ((b₁ ∸ b₂) + l))  ≡⟨ by lemma₂ ⟩≈
    ⟦ r ⟧ empty (max b₁ b₂ + l)         ∎≈
  where
  lemma₀ = λ b₁ b₂ l →
    max b₁ b₂ + l         ≡⟨ by (max≡+∸ b₁) ⟩
    b₁ + (b₂ ∸ b₁) + l    ≡⟨ by (+-assoc b₁) ⟩∎
    b₁ + ((b₂ ∸ b₁) + l)  ∎

  lemma₂ = λ l →
    b₂ + ((b₁ ∸ b₂) + l)  ≡⟨ by (lemma₀ b₂) ⟩
    max b₂ b₁ + l         ≡⟨ by (max-comm b₂) ⟩∎
    max b₁ b₂ + l         ∎

  lemma₃ = λ l →
    b₁ + ((b₂ ∸ b₁) + l)  ≡⟨ by (lemma₀ b₁) ⟩
    max b₁ b₂ + l         ≡⟨ by lemma₂ ⟩∎
    b₂ + ((b₁ ∸ b₂ + l))  ∎

-- The relation is compatible with respect to [] and deallocate ∷_.

[]-cong : [] ≘ []
[]-cong = 0 , λ _ → W.reflexive _

deallocate∷-cong :
  ∀ {p q} → force p ≘ force q → deallocate ∷ p ≘ deallocate ∷ q
deallocate∷-cong (b , p≈q) = b , λ l → later λ { .force → p≈q l }

-- However, it is not compatible with respect to allocate ∷_.

¬allocate∷-cong :
  ¬ (∀ {p q} → force p ≘ force q → allocate ∷ p ≘ allocate ∷ q)
¬allocate∷-cong hyp = ¬a∷p≘a∷q a∷p≘a∷q
  where
  p q : Colist′ Stmt ∞
  p = λ { .force → allocate ∷ λ { .force → [] } }
  q = λ { .force → deallocate ∷ p }

  p≘q : force p ≘ force q
  p≘q = 0 , λ where
    zero    → laterʳ now
    (suc l) → later λ { .force → laterʳ now }

  a∷p≘a∷q : allocate ∷ p ≘ allocate ∷ q
  a∷p≘a∷q = hyp p≘q

  2≢1 : ¬ now (just (record { size = 2 })) ≈
          now (just (record { size = 1 }))
  2≢1 ()

  a∷p≉a∷q : ∀ {l} → ¬ ⟦ allocate ∷ p ⟧ empty (2 + l) ≈
                      ⟦ allocate ∷ q ⟧ empty (2 + l)
  a∷p≉a∷q hyp = 2≢1 (laterʳ⁻¹ (later⁻¹ (later⁻¹ hyp)))

  ¬a∷p≘a∷q : ¬ allocate ∷ p ≘ allocate ∷ q
  ¬a∷p≘a∷q (zero        , a∷p≈a∷q) = a∷p≉a∷q (a∷p≈a∷q 2)
  ¬a∷p≘a∷q (suc zero    , a∷p≈a∷q) = a∷p≉a∷q (a∷p≈a∷q 1)
  ¬a∷p≘a∷q (suc (suc _) , a∷p≈a∷q) = a∷p≉a∷q (a∷p≈a∷q 0)

------------------------------------------------------------------------
-- Some examples

-- A crashing computation.

crash : Delay (Maybe Heap) ∞
crash = now nothing

-- A program that runs in constant space.

constant-space : ∀ {i} → Program i
constant-space =
  allocate   ∷ λ { .force →
  deallocate ∷ λ { .force →
  constant-space }}

-- Another program that runs in constant space.

constant-space₂ : ∀ {i} → Program i
constant-space₂ =
  allocate   ∷ λ { .force →
  allocate   ∷ λ { .force →
  deallocate ∷ λ { .force →
  deallocate ∷ λ { .force →
  constant-space₂ }}}}

-- A program that does not run in bounded space.

unbounded-space : ∀ {i} → Program i
unbounded-space = allocate ∷ λ { .force → unbounded-space }

-- The program constant-space crashes when the heap size limit is 0.

constant-space-crash : ⟦ constant-space ⟧ empty 0 ≈ crash
constant-space-crash = now

-- However, for positive heap size limits the program loops.

constant-space-loop :
  ∀ {i limit} → [ i ] ⟦ constant-space ⟧ empty (suc limit) ≈ never
constant-space-loop =
  later λ { .force →
  later λ { .force →
  constant-space-loop }}

-- The program constant-space₂ loops when the heap size is at least 2.

constant-space₂-loop :
  ∀ {i limit} → [ i ] ⟦ constant-space₂ ⟧ empty (2 + limit) ≈ never
constant-space₂-loop =
  later λ { .force →
  later λ { .force →
  later λ { .force →
  later λ { .force →
  constant-space₂-loop }}}}

-- The program unbounded-space crashes for all heap size limits.

unbounded-space-crash :
  ∀ limit → ⟦ unbounded-space ⟧ empty limit ≈ crash
unbounded-space-crash limit =
  subst (λ s → ⟦ unbounded-space ⟧ (heap s) limit ≈ crash)
        (∸≡0 limit)
        (helper limit ≤-refl)
  where
  heap : ℕ → Heap
  heap n = record { size = n }

  helper :
    ∀ {i} n → n ≤ limit →
    [ i ] ⟦ unbounded-space ⟧ (heap (limit ∸ n)) limit ≈ crash
  helper n       n≤limit with (limit ∸ n) ≟ limit
  helper _       _       | yes _           = now
  helper zero    _       | no  limit≢limit = ⊥-elim (limit≢limit refl)
  helper (suc n) n<limit | no  _     rewrite sym (∸≡suc∸suc n<limit) =
    laterˡ (helper n (<→≤ n<limit))

-- The programs constant-space and constant-space₂ are ≘-equivalent.

constant-space≘constant-space₂ : constant-space ≘ constant-space₂
constant-space≘constant-space₂ =
  2 , λ l →
    ⟦ constant-space ⟧ empty (2 + l)   ≈⟨ constant-space-loop ⟩
    never                              ≈⟨ W.symmetric constant-space₂-loop ⟩∎
    ⟦ constant-space₂ ⟧ empty (2 + l)  ∎

-- The programs constant-space and unbounded-space are not
-- ≘-equivalent.

¬constant-space≘unbounded-space : ¬ constant-space ≘ unbounded-space
¬constant-space≘unbounded-space (b , c≈u) = now≉never (
  now nothing                        ≈⟨ W.symmetric (unbounded-space-crash (b + 1)) ⟩
  ⟦ unbounded-space ⟧ empty (b + 1)  ≈⟨ W.symmetric (c≈u 1) ⟩
  ⟦ constant-space ⟧ empty (b + 1)   ≡⟨ by (+-comm b) ⟩≈
  ⟦ constant-space ⟧ empty (1 + b)   ≈⟨ constant-space-loop ⟩∎
  never                              ∎)
