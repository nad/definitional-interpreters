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

open import Only-allocation

------------------------------------------------------------------------
-- Heaps

-- Bounded heaps. (Only a size, plus a proof showing that the size is
-- bounded.)

record Heap (limit : ℕ) : Set where
  field
    size    : ℕ
    bounded : size ≤ limit

open Heap public

-- An empty heap.

empty : ∀ {limit} → Heap limit
empty = record { size = zero; bounded = zero≤ _ }

-- A full heap.

full : ∀ limit → Heap limit
full limit = record { size = limit; bounded = ≤-refl }

-- Reduces the heap's size by one. If the heap is empty, then it is
-- returned unchanged.

shrink : ∀ {limit} → Heap limit → Heap limit
shrink {limit} h = record h
  { size    = pred (size h)
  ; bounded = pred (size h)  ≤⟨ pred≤ _ ⟩
              size h         ≤⟨ bounded h ⟩∎
              limit          ∎≤
  }

-- Increases the heap's size by one. If the heap already has the
-- maximum size, then nothing is returned.

grow : ∀ {limit} → Heap limit → Maybe (Heap limit)
grow {limit} h = case ≤⊎> limit (size h) of λ where
  (inj₁ _)   → nothing
  (inj₂ h<l) → just (record h { size    = suc (size h)
                              ; bounded = h<l
                              })

-- Lemmas related to grow.

grow-full :
  ∀ {limit} (h : Heap limit) → size h ≡ limit → grow h ≡ nothing
grow-full {limit} h h≡l with ≤⊎> limit (size h)
... | inj₁ _   = refl
... | inj₂ h<l =
  ⊥-elim (+≮ 0 (
    1 + size h  ≤⟨ h<l ⟩
    limit       ≡⟨ sym h≡l ⟩≤
    size h      ∎≤))

grow-not-full :
  ∀ {limit} (h : Heap limit) →
  size h < limit → ∃ λ h′ → grow h ≡ just h′ × size h′ ≡ 1 + size h
grow-not-full {limit} h h<l with ≤⊎> limit (size h)
... | inj₂ _   = _ , refl , refl
... | inj₁ l≤h =
  ⊥-elim (+≮ 0 (
    1 + size h  ≤⟨ h<l ⟩
    limit       ≤⟨ l≤h ⟩∎
    size h      ∎≤))

------------------------------------------------------------------------
-- Definitional interpreter

-- One step of computation.

step : ∀ {limit} → Stmt → Heap limit → Maybe (Heap limit)
step deallocate heap = just (shrink heap)
step allocate   heap = grow heap

-- A definitional interpreter.

⟦_⟧ : ∀ {i limit} →
      Program ∞ → Heap limit → Delay (Maybe (Heap limit)) i
⟦ []    ⟧ heap = now (just heap)
⟦ s ∷ p ⟧ heap =
  case step s heap of λ where
    nothing     → now nothing
    (just heap) → later λ { .force → ⟦ force p ⟧ heap }

------------------------------------------------------------------------
-- A program equivalence

-- An equivalence relation that identifies programs that, given a
-- sufficient amount of memory, behave identically (up to weak
-- bisimilarity).

infix 4 _≘_

_≘_ : Program ∞ → Program ∞ → Set
p ≘ q =
  ∃ λ bound →
  ∀ limit (h : Heap limit) →
  bound + size h ≤ limit →
  ⟦ p ⟧ h ≈ ⟦ q ⟧ h

-- The relation is an equivalence relation.

reflexive : ∀ {p} → p ≘ p
reflexive = 0 , λ _ _ _ → W.reflexive _

symmetric : ∀ {p q} → p ≘ q → q ≘ p
symmetric = Σ-map id λ hyp l h b → W.symmetric (hyp l h b)

transitive : ∀ {p q r} → p ≘ q → q ≘ r → p ≘ r
transitive {p} {q} {r} (b₁ , p₁) (b₂ , p₂) =
  max b₁ b₂ , λ l h b →
    ⟦ p ⟧ h  ≈⟨ p₁ l h (lemma₁ l h b) ⟩
    ⟦ q ⟧ h  ≈⟨ p₂ l h (lemma₂ l h b) ⟩∎
    ⟦ r ⟧ h  ∎
  where
  lemma₁ = λ l h b →
    b₁ + size h         ≤⟨ ˡ≤max b₁ _ +-mono ≤-refl ⟩
    max b₁ b₂ + size h  ≤⟨ b ⟩∎
    l                   ∎≤

  lemma₂ = λ l h b →
    b₂ + size h         ≤⟨ ʳ≤max b₁ _ +-mono ≤-refl ⟩
    max b₁ b₂ + size h  ≤⟨ b ⟩∎
    l                   ∎≤

-- The relation is compatible with respect to the program formers.

[]-cong : [] ≘ []
[]-cong = 0 , λ _ _ _ → W.reflexive _

∷-cong : ∀ {s p q} → force p ≘ force q → s ∷ p ≘ s ∷ q
∷-cong {deallocate} (b , p≈q) =
  b , λ l h b≤ → later λ { .force → p≈q l (shrink h) (
        b + size (shrink h)  ≤⟨ ≤-refl {n = b} +-mono pred≤ _ ⟩
        b + size h           ≤⟨ b≤ ⟩
        l                    ∎≤) }
∷-cong {allocate} {p} {q} (b , p≈q) = 1 + b , lemma
  where
  lemma : ∀ l (h : Heap l) → 1 + b + size h ≤ l →
          ⟦ allocate ∷ p ⟧ h ≈ ⟦ allocate ∷ q ⟧ h
  lemma l h 1+b≤ with ≤⊎> l (size h)
  ... | inj₁ _   = now
  ... | inj₂ h<l = later λ { .force → p≈q l _ (
                     b + (1 + size h)  ≡⟨ +-assoc b ⟩≤
                     b + 1 + size h    ≡⟨ by (+-comm b) ⟩≤
                     1 + b + size h    ≤⟨ 1+b≤ ⟩∎
                     l                 ∎≤) }

------------------------------------------------------------------------
-- Some examples

-- A crashing computation.

crash : ∀ {l} → Delay (Maybe (Heap l)) ∞
crash = now nothing

-- The program constant-space crashes when the heap is full.

constant-space-crash :
  ∀ {limit} (h : Heap limit) →
  size h ≡ limit →
  ⟦ constant-space ⟧ h ≈ crash
constant-space-crash h h≡l
  rewrite grow-full h h≡l =
  now

-- However, for smaller heaps the program loops.

constant-space-loop :
  ∀ {i limit} (h : Heap limit) →
  size h < limit →
  [ i ] ⟦ constant-space ⟧ h ≈ never
constant-space-loop {limit = limit} h <limit
  with grow h | grow-not-full h <limit
... | .(just h′) | h′ , refl , refl =
  later λ { .force →
  later λ { .force →
  constant-space-loop _ <limit }}

-- The program constant-space₂ loops when there are at least two empty
-- slots in the heap.

constant-space₂-loop :
  ∀ {i limit} (h : Heap limit) →
  2 + size h ≤ limit →
  [ i ] ⟦ constant-space₂ ⟧ h ≈ never
constant-space₂-loop {i} {limit} h 2+h≤limit
  with grow h | grow-not-full h (<→≤ 2+h≤limit)
... | .(just h′) | h′ , refl , refl = later λ { .force → lemma }
  where
  lemma : [ i ] ⟦ force (tail constant-space₂) ⟧ h′ ≈ never
  lemma with grow h′ | grow-not-full h′ 2+h≤limit
  lemma | .(just h″) | h″ , refl , refl =
    later λ { .force →
    later λ { .force →
    later λ { .force →
    constant-space₂-loop _ 2+h≤limit }}}

-- The program unbounded-space crashes for all heaps.

unbounded-space-crash :
  ∀ {limit} (h : Heap limit) → ⟦ unbounded-space ⟧ h ≈ crash
unbounded-space-crash {limit} h = helper h (≤→≤↑ (bounded h))
  where
  helper :
    ∀ {i} (h′ : Heap limit) → size h′ ≤↑ limit →
    [ i ] ⟦ unbounded-space ⟧ h′ ≈ crash
  helper h′ (≤↑-refl h′≡l)
    rewrite grow-full h′ h′≡l =
    now
  helper h′ (≤↑-step 1+h′≤l)
    with grow h′ | grow-not-full h′ (≤↑→≤ 1+h′≤l)
  ... | .(just h″) | h″ , refl , refl =
    laterˡ (helper h″ 1+h′≤l)

-- The programs constant-space and constant-space₂ are ≘-equivalent.

constant-space≘constant-space₂ : constant-space ≘ constant-space₂
constant-space≘constant-space₂ =
  2 , λ l h 2+h≤l →
    ⟦ constant-space ⟧ h   ≈⟨ constant-space-loop _ (<→≤ 2+h≤l) ⟩
    never                  ≈⟨ W.symmetric (constant-space₂-loop _ 2+h≤l) ⟩∎
    ⟦ constant-space₂ ⟧ h  ∎

-- The programs constant-space and unbounded-space are not
-- ≘-equivalent.

¬constant-space≘unbounded-space : ¬ constant-space ≘ unbounded-space
¬constant-space≘unbounded-space (b , c≈u) = now≉never (
  crash                  ≈⟨ W.symmetric (unbounded-space-crash h) ⟩
  ⟦ unbounded-space ⟧ h  ≈⟨ W.symmetric (c≈u _ h (≤-refl +-mono zero≤ _)) ⟩
  ⟦ constant-space ⟧ h   ≈⟨ constant-space-loop h (m≤n+m _ _) ⟩∎
  never                  ∎)
  where
  h : Heap (b + 1)
  h = record
    { size    = 0
    ; bounded = zero≤ _
    }
