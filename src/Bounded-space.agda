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
open import Delay-monad.Weak-bisimilarity
open import Equality.Propositional
open import Prelude

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

-- The program unbounded-space crashes for all heap size limits.

unbounded-space-crash :
  ∀ {limit} → ⟦ unbounded-space ⟧ empty limit ≈ crash
unbounded-space-crash {limit} =
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
