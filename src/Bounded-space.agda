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
open import Delay-monad.Bisimilarity as B
  hiding (reflexive; symmetric)
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
grow {limit} h = case limit ≤⊎> size h of λ where
  (inj₁ _)   → nothing
  (inj₂ h<l) → just (record h { size    = suc (size h)
                              ; bounded = h<l
                              })

-- Lemmas related to grow.

grow-full :
  ∀ {limit} (h : Heap limit) → size h ≡ limit → grow h ≡ nothing
grow-full {limit} h h≡l with limit ≤⊎> size h
... | inj₁ _   = refl
... | inj₂ h<l =
  ⊥-elim (+≮ 0 (
    1 + size h  ≤⟨ h<l ⟩
    limit       ≡⟨ sym h≡l ⟩≤
    size h      ∎≤))

grow-not-full :
  ∀ {limit} (h : Heap limit) →
  size h < limit → ∃ λ h′ → grow h ≡ just h′ × size h′ ≡ 1 + size h
grow-not-full {limit} h h<l with limit ≤⊎> size h
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

infix 4 [_]_≃_ [_]_≃′_

[_]_≃_ : Size → Program ∞ → Program ∞ → Set
[ i ] p ≃ q =
  ∃ λ c →
  ∀ l (h : Heap l) →
  c + h .size ≤ l →
  [ i ] ⟦ p ⟧ h ≈ ⟦ q ⟧ h

[_]_≃′_ : Size → Program ∞ → Program ∞ → Set
[ i ] p ≃′ q =
  ∃ λ c →
  ∀ l (h : Heap l) →
  c + h .size ≤ l →
  [ i ] ⟦ p ⟧ h ≈′ ⟦ q ⟧ h

-- The relation is an equivalence relation.

reflexive : ∀ {i p} → [ i ] p ≃ p
reflexive = 0 , λ _ _ _ → B.reflexive _

symmetric : ∀ {i p q} → [ i ] p ≃ q → [ i ] q ≃ p
symmetric = Σ-map id λ hyp l h c → B.symmetric (hyp l h c)

transitive : ∀ {i p q r} → [ ∞ ] p ≃ q → [ ∞ ] q ≃ r → [ i ] p ≃ r
transitive {p = p} {q} {r} (c₁ , p₁) (c₂ , p₂) =
  max c₁ c₂ , λ l h c →
    ⟦ p ⟧ h  ≈⟨ p₁ l h (lemma₁ l h c) ⟩
    ⟦ q ⟧ h  ≈⟨ p₂ l h (lemma₂ l h c) ⟩∎
    ⟦ r ⟧ h  ∎
  where
  lemma₁ = λ l h c →
    c₁ + h .size         ≤⟨ ˡ≤max c₁ _ +-mono ≤-refl ⟩
    max c₁ c₂ + h .size  ≤⟨ c ⟩∎
    l                   ∎≤

  lemma₂ = λ l h c →
    c₂ + h .size         ≤⟨ ʳ≤max c₁ _ +-mono ≤-refl ⟩
    max c₁ c₂ + h .size  ≤⟨ c ⟩∎
    l                   ∎≤

-- The relation is compatible with respect to the program formers.

[]-cong : ∀ {i} → [ i ] [] ≃ []
[]-cong = 0 , λ _ _ _ → B.reflexive _

∷-cong : ∀ {s p q i} → [ i ] p .force ≃′ q .force → [ i ] s ∷ p ≃ s ∷ q
∷-cong {deallocate} (c , p≈q) =
  c , λ l h c≤ → later λ { .force → p≈q l (shrink h) (
        c + shrink h .size  ≤⟨ ≤-refl {n = c} +-mono pred≤ _ ⟩
        c + h .size         ≤⟨ c≤ ⟩
        l                   ∎≤) .force }
∷-cong {allocate} {p} {q} {i} (c , p≈q) = 1 + c , lemma
  where
  lemma : ∀ l (h : Heap l) → 1 + c + h .size ≤ l →
          [ i ] ⟦ allocate ∷ p ⟧ h ≈ ⟦ allocate ∷ q ⟧ h
  lemma l h 1+c≤ with l ≤⊎> h .size
  ... | inj₁ _   = now
  ... | inj₂ h<l = later λ { .force → p≈q l _ (
                     c + (1 + h .size)  ≡⟨ +-assoc c ⟩≤
                     c + 1 + h .size    ≡⟨ by (+-comm c) ⟩≤
                     1 + c + h .size    ≤⟨ 1+c≤ ⟩∎
                     l                  ∎≤) .force }

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

-- The programs constant-space and constant-space₂ are ≃-equivalent.

constant-space≃constant-space₂ : [ ∞ ] constant-space ≃ constant-space₂
constant-space≃constant-space₂ =
  2 , λ l h 2+h≤l →
    ⟦ constant-space ⟧ h   ≈⟨ constant-space-loop _ (<→≤ 2+h≤l) ⟩
    never                  ≈⟨ B.symmetric (constant-space₂-loop _ 2+h≤l) ⟩∎
    ⟦ constant-space₂ ⟧ h  ∎

-- The programs constant-space and unbounded-space are not
-- ≃-equivalent.

¬constant-space≃unbounded-space :
  ¬ [ ∞ ] constant-space ≃ unbounded-space
¬constant-space≃unbounded-space (c , c≈u) = now≉never (
  crash                  ≈⟨ B.symmetric (unbounded-space-crash h) ⟩
  ⟦ unbounded-space ⟧ h  ≈⟨ B.symmetric (c≈u _ h (≤-refl +-mono zero≤ _)) ⟩
  ⟦ constant-space ⟧ h   ≈⟨ constant-space-loop h (m≤n+m _ _) ⟩∎
  never                  ∎)
  where
  h : Heap (c + 1)
  h = record
    { size    = 0
    ; bounded = zero≤ _
    }
