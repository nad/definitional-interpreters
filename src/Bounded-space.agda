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

module Bounded-space where

open import Equality.Propositional
open import Prelude
open import Tactic.By.Propositional
open import Prelude.Size

open import Colist equality-with-J
open import Nat equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity as B
  hiding (reflexive; symmetric)

open import Only-allocation

------------------------------------------------------------------------
-- Heaps

-- Bounded heaps. (Only a size, plus a proof showing that the size is
-- bounded.)

record Heap (limit : ℕ) : Type where
  field
    size  : ℕ
    bound : size ≤ limit

open Heap public

-- An empty heap.

empty : ∀ {l} → Heap l
empty = record { size = zero; bound = zero≤ _ }

-- A full heap.

full : ∀ l → Heap l
full l = record { size = l; bound = ≤-refl }

-- Reduces the heap's size by one. If the heap is empty, then it is
-- returned unchanged.

shrink : ∀ {l} → Heap l → Heap l
shrink {l} h = record
  { size  = pred (h .size)
  ; bound = pred (h .size)  ≤⟨ pred≤ _ ⟩
            h .size         ≤⟨ h .bound ⟩∎
            l               ∎≤
  }

-- Increases the heap's size by one. If the heap already has the
-- maximum size, then nothing is returned.

grow : ∀ {l} → Heap l → Maybe (Heap l)
grow {l} h with l ≤⊎> h .size
... | inj₁ _   = nothing
... | inj₂ h<l = just (record { size  = suc (h .size)
                              ; bound = h<l
                              })

-- Lemmas related to grow.

grow-full :
  ∀ {l} (h : Heap l) → h .size ≡ l → grow h ≡ nothing
grow-full {l} h h≡l with l ≤⊎> h .size
... | inj₁ _   = refl
... | inj₂ h<l =
  ⊥-elim (+≮ 0 (
    1 + h .size  ≤⟨ h<l ⟩
    l            ≡⟨ sym h≡l ⟩≤
    h .size      ∎≤))

grow-not-full :
  ∀ {l} (h : Heap l) →
  h .size < l → ∃ λ h′ → grow h ≡ just h′ × h′ .size ≡ 1 + h .size
grow-not-full {l} h h<l with l ≤⊎> h .size
... | inj₂ _   = _ , refl , refl
... | inj₁ l≤h =
  ⊥-elim (+≮ 0 (
    1 + h .size  ≤⟨ h<l ⟩
    l            ≤⟨ l≤h ⟩∎
    h .size      ∎≤))

------------------------------------------------------------------------
-- Definitional interpreter

-- One step of computation.

step : ∀ {l} → Stmt → Heap l → Maybe (Heap l)
step dealloc heap = just (shrink heap)
step alloc   heap = grow heap

-- A crashing computation.

crash : ∀ {i l} → Delay (Maybe (Heap l)) i
crash = now nothing

-- A definitional interpreter.

⟦_⟧ : ∀ {i l} → Program i → Heap l → Delay (Maybe (Heap l)) i
⟦ []    ⟧ heap = now (just heap)
⟦ s ∷ p ⟧ heap with step s heap
... | nothing       = crash
... | just new-heap = later λ { .force → ⟦ p .force ⟧ new-heap }

------------------------------------------------------------------------
-- A program equivalence

-- An equivalence relation that identifies programs that, given a
-- sufficient amount of memory, behave identically (up to weak
-- bisimilarity).

infix 4 [_]_≃_ [_]_≃′_

[_]_≃_ : Size → Program ∞ → Program ∞ → Type
[ i ] p ≃ q =
  ∃ λ c →
  ∀ l (h : Heap l) →
  c + h .size ≤ l →
  [ i ] ⟦ p ⟧ h ≈ ⟦ q ⟧ h

[_]_≃′_ : Size → Program ∞ → Program ∞ → Type
[ i ] p ≃′ q =
  ∃ λ c →
  ∀ l (h : Heap l) →
  c + h .size ≤ l →
  [ i ] ⟦ p ⟧ h ≈′ ⟦ q ⟧ h

-- The relation is an equivalence relation.

reflexive : ∀ {i} p → [ i ] p ≃ p
reflexive _ = 0 , λ _ _ _ → B.reflexive _

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
[]-cong = reflexive []

∷-cong : ∀ {s p q i} → [ i ] p .force ≃′ q .force → [ i ] s ∷ p ≃ s ∷ q
∷-cong {dealloc} (c , p≈q) =
  c , λ l h c≤ → later λ { .force → p≈q l (shrink h) (
        c + shrink h .size  ≤⟨ ≤-refl {n = c} +-mono pred≤ _ ⟩
        c + h .size         ≤⟨ c≤ ⟩
        l                   ∎≤) .force }
∷-cong {alloc} {p} {q} {i} (c , p≈q) = 1 + c , lemma
  where
  lemma : ∀ l (h : Heap l) → 1 + c + h .size ≤ l →
          [ i ] ⟦ alloc ∷ p ⟧ h ≈ ⟦ alloc ∷ q ⟧ h
  lemma l h 1+c≤ with l ≤⊎> h .size
  ... | inj₁ _   = now
  ... | inj₂ h<l = later λ { .force → p≈q l _ (
                     c + (1 + h .size)  ≡⟨ +-assoc c ⟩≤
                     c + 1 + h .size    ≡⟨ by (+-comm c) ⟩≤
                     1 + c + h .size    ≤⟨ 1+c≤ ⟩∎
                     l                  ∎≤) .force }

------------------------------------------------------------------------
-- Some examples

-- The program bounded crashes when the heap is full.

bounded-crash :
  ∀ {i l} (h : Heap l) →
  h .size ≡ l →
  [ i ] ⟦ bounded ⟧ h ≈ crash
bounded-crash h h≡l
  rewrite grow-full h h≡l =
  now

-- However, for smaller heaps the program loops.

bounded-loop :
  ∀ {i l} (h : Heap l) →
  h .size < l →
  [ i ] ⟦ bounded ⟧ h ≈ never
bounded-loop {l = l} h <l
  with grow h | grow-not-full h <l
... | .(just h′) | h′ , refl , refl =
  later λ { .force →
  later λ { .force →
  bounded-loop _ <l }}

-- The program bounded₂ loops when there are at least two empty slots
-- in the heap.

bounded₂-loop :
  ∀ {i l} (h : Heap l) →
  2 + h .size ≤ l →
  [ i ] ⟦ bounded₂ ⟧ h ≈ never
bounded₂-loop {i} {l} h 2+h≤l
  with grow h | grow-not-full h (<→≤ 2+h≤l)
... | .(just h′) | h′ , refl , refl = later λ { .force → lemma }
  where
  lemma : [ i ] ⟦ force (tail bounded₂) ⟧ h′ ≈ never
  lemma with grow h′ | grow-not-full h′ 2+h≤l
  lemma | .(just h″) | h″ , refl , refl =
    later λ { .force →
    later λ { .force →
    later λ { .force →
    bounded₂-loop _ 2+h≤l }}}

-- The program unbounded crashes for all heaps.

unbounded-crash :
  ∀ {i l} (h : Heap l) → [ i ] ⟦ unbounded ⟧ h ≈ crash
unbounded-crash {l = l} h = helper h (≤→≤↑ (h .bound))
  where
  helper :
    ∀ {i} (h′ : Heap l) → size h′ ≤↑ l →
    [ i ] ⟦ unbounded ⟧ h′ ≈ crash
  helper h′ (≤↑-refl h′≡l)
    rewrite grow-full h′ h′≡l =
    now
  helper h′ (≤↑-step 1+h′≤l)
    with grow h′ | grow-not-full h′ (≤↑→≤ 1+h′≤l)
  ... | .(just h″) | h″ , refl , refl =
    laterˡ (helper h″ 1+h′≤l)

-- The programs bounded and bounded₂ are ≃-equivalent.

bounded≃bounded₂ : [ ∞ ] bounded ≃ bounded₂
bounded≃bounded₂ =
  2 , λ l h 2+h≤l →
    ⟦ bounded ⟧ h   ≈⟨ bounded-loop _ (<→≤ 2+h≤l) ⟩
    never           ≈⟨ B.symmetric (bounded₂-loop _ 2+h≤l) ⟩∎
    ⟦ bounded₂ ⟧ h  ∎

-- The programs bounded and unbounded are not ≃-equivalent.

¬bounded≃unbounded :
  ¬ [ ∞ ] bounded ≃ unbounded
¬bounded≃unbounded (c , c≈u) = now≉never (
  crash            ≈⟨ B.symmetric (unbounded-crash h) ⟩
  ⟦ unbounded ⟧ h  ≈⟨ B.symmetric (c≈u _ h (≤-refl +-mono zero≤ _)) ⟩
  ⟦ bounded ⟧ h    ≈⟨ bounded-loop h (m≤n+m _ _) ⟩∎
  never            ∎)
  where
  h : Heap (c + 1)
  h = record
    { size  = 0
    ; bound = zero≤ _
    }
