------------------------------------------------------------------------
-- Definitional interpreters can model systems with unbounded space
------------------------------------------------------------------------

-- As a follow-up to the development in Bounded-space I asked Ancona,
-- Dagnino and Zucca for further examples of properties for which it
-- is not clear to them if definitional interpreters work well. They
-- asked for a semantics that returns the largest heap size used by
-- the program, or infinity if there is no bound on this size. They
-- also asked how one can prove that a program transformation does not
-- increase the maximum heap usage.

-- It is impossible to write an Agda program that computes the maximum
-- heap usage, but one can at least produce a potentially infinite
-- list containing all heap sizes encountered in the execution of a
-- program, and then reason about this list. This approach is taken
-- below.

{-# OPTIONS --without-K --safe #-}

module Unbounded-space where

open import Colist
open import Conat hiding (pred) renaming (_+_ to _⊕_; _∸_ to _⊖_)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Omniscience
open import Prelude
open import Tactic.By

open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import Nat equality-with-J as Nat using (_≤_; _≤↑_; _<_; pred)

import Bounded-space

------------------------------------------------------------------------
-- Programs

open Bounded-space public using (Stmt; Program)
open Stmt public

------------------------------------------------------------------------
-- Heaps

-- Heaps. (Only sizes.)

Heap : Set
Heap = ℕ

-- Modifies the heap according to the given instruction.

modify : Stmt → Heap → Heap
modify allocate   = suc
modify deallocate = pred

------------------------------------------------------------------------
-- Definitional interpreter

-- A definitional interpreter. It returns a trace of all heap sizes
-- encountered during the program's run. The input is the initial heap
-- size.

mutual

  ⟦_⟧ : ∀ {i} → Program ∞ → ℕ → Colist ℕ i
  ⟦ p ⟧ h = h ∷ ⟦ p ⟧′ h

  ⟦_⟧′ : ∀ {i} → Program ∞ → ℕ → Colist′ ℕ i
  force (⟦ []    ⟧′ h) = []
  force (⟦ s ∷ p ⟧′ h) = ⟦ force p ⟧ (modify s h)

------------------------------------------------------------------------
-- Upper bounds

-- [ ∞ ] ms ⊑ n means that n is an upper bound of every number in ms.

infix 4 [_]_⊑_

[_]_⊑_ : Size → Colist ℕ ∞ → Conat ∞ → Set
[ i ] ms ⊑ n = □ i (λ m → [ ∞ ] ⌜ m ⌝ ≤ n) ms

-- The conatural number infinity is always an upper bound.

infix 4 _⊑infinity

_⊑infinity : ∀ {i} ns → [ i ] ns ⊑ infinity
_⊑infinity = □-replicate (_≤infinity ∘ ⌜_⌝)

-- A form of transitivity.

transitive-⊑≤ :
  ∀ {i ms n o} → [ i ] ms ⊑ n → [ ∞ ] n ≤ o → [ i ] ms ⊑ o
transitive-⊑≤ p q = □-map (flip transitive-≤ q) p

-- Another form of transitivity.

transitive-◇≤⊑ :
  ∀ {m ns o} → ◇ (m ≤_) ns → [ ∞ ] ns ⊑ o → [ ∞ ] ⌜ m ⌝ ≤ o
transitive-◇≤⊑ {m} {ns} {o} = curry (
  ◇ (m ≤_) ns × [ ∞ ] ns ⊑ o         ↝⟨ Σ-map id swap ∘ uncurry □◇-witness ∘ swap ⟩
  (∃ λ n → m ≤ n × [ ∞ ] ⌜ n ⌝ ≤ o)  ↝⟨ (λ { (_ , m≤n , n≤o) → transitive-≤ (⌜⌝-mono m≤n) n≤o }) ⟩□
  [ ∞ ] ⌜ m ⌝ ≤ o                    □)

-- If m is an upper bound of ms, and no natural number is an upper
-- bound, then m is bisimilar to infinity.

no-finite→infinite :
  ∀ {m ms} →
  (∀ n → ¬ [ ∞ ] ms ⊑ ⌜ n ⌝) →
  [ ∞ ] ms ⊑ m →
  Conat.[ ∞ ] m ∼ infinity
no-finite→infinite {m} {ms} no-finite =
  [ ∞ ] ms ⊑ m               ↝⟨ (λ ms⊑n → uncurry λ n →

      Conat.[ ∞ ] m ∼ ⌜ n ⌝        ↝⟨ ∼→≤ ⟩
      [ ∞ ] m ≤ ⌜ n ⌝              ↝⟨ transitive-⊑≤ ms⊑n ⟩
      [ ∞ ] ms ⊑ ⌜ n ⌝             ↝⟨ no-finite n ⟩□
      ⊥                            □) ⟩

  Infinite m                 ↝⟨ Infinite→∼infinity ⟩□
  Conat.[ ∞ ] m ∼ infinity   □

-- The number n is an upper bound of the heap size required for a
-- program when it is started with an empty heap iff, for any initial
-- heap h, n plus the size of h is an upper bound.
--
-- Note that this kind of property might not hold for a more
-- complicated programming language, in which a program's actions
-- could depend on the contents of the initial heap.

∀⟦⟧⊑⇔⟦⟧⊑ :
  ∀ {p n i} →
  [ i ] ⟦ p ⟧ 0 ⊑ n ⇔ (∀ h → [ i ] ⟦ p ⟧ h ⊑ n ⊕ ⌜ h ⌝)
∀⟦⟧⊑⇔⟦⟧⊑ {p} {n} {i} = record
  { to   = to p
  ; from = (∀ h → [ i ] ⟦ p ⟧ h ⊑ n ⊕ ⌜ h ⌝)  ↝⟨ _$ 0 ⟩
           [ i ] ⟦ p ⟧ 0 ⊑ n ⊕ ⌜ 0 ⌝          ↝⟨ flip transitive-⊑≤ (∼→≤ (+-right-identity _)) ⟩□
           [ i ] ⟦ p ⟧ 0 ⊑ n                  □
  }
  where
  +⊕-cong :
    ∀ {m₁ m₂ n i} → [ i ] ⌜ m₁ ⌝ ≤ m₂ → [ i ] ⌜ m₁ + n ⌝ ≤ m₂ ⊕ ⌜ n ⌝
  +⊕-cong {m₁} {m₂} {n} {i} =
    [ i ] ⌜ m₁ ⌝ ≤ m₂                  ↝⟨ _+-mono reflexive-≤ _ ⟩
    [ i ] ⌜ m₁ ⌝ ⊕ ⌜ n ⌝ ≤ m₂ ⊕ ⌜ n ⌝  ↝⟨ transitive-≤ (∼→≤ (⌜⌝-+ m₁)) ⟩□
    [ i ] ⌜ m₁ + n ⌝ ≤ m₂ ⊕ ⌜ n ⌝      □

  to : ∀ {m i} p →
       [ i ] ⟦ p ⟧ m ⊑ n → ∀ h → [ i ] ⟦ p ⟧ (m + h) ⊑ n ⊕ ⌜ h ⌝
  to []      (m≤n ∷ _)  _ = +⊕-cong m≤n ∷ λ { .force → [] }
  to (s ∷ p) (m≤n ∷ p⊑) h = +⊕-cong m≤n ∷ λ { .force →
                              to′ _ s (force p⊑) }
    where
    to′ : ∀ {i} m s →
          [ i ] ⟦ force p ⟧ (modify s m)       ⊑ n →
          [ i ] ⟦ force p ⟧ (modify s (m + h)) ⊑ n ⊕ ⌜ h ⌝
    to′ _       allocate   p⊑ = to (force p) p⊑ h
    to′ (suc m) deallocate p⊑ = to (force p) p⊑ h
    to′ zero    deallocate p⊑ = transitive-⊑≤ (to (force p) p⊑ (pred h))
                                              (reflexive-≤ n
                                                 +-mono
                                               ⌜⌝-mono (Nat.pred≤ _))

------------------------------------------------------------------------
-- Least upper bounds

-- The least upper bound of a colist of natural numbers.

Least-upper-bound : Size → Colist ℕ ∞ → Conat ∞ → Set
Least-upper-bound i ns n =
  [ i ] ns ⊑ n
    ×
  (∀ n′ → [ ∞ ] ns ⊑ n′ → [ i ] n ≤ n′)

-- Least upper bounds are unique.

lub-unique :
  ∀ {ns n₁ n₂ i} →
  Least-upper-bound ∞ ns n₁ → Least-upper-bound ∞ ns n₂ →
  Conat.[ i ] n₁ ∼ n₂
lub-unique (lub₁₁ , lub₁₂) (lub₂₁ , lub₂₂) =
  antisymmetric-≤ (lub₁₂ _ lub₂₁) (lub₂₂ _ lub₁₁)

------------------------------------------------------------------------
-- The maximum heap usage predicate

-- The smallest heap size that is required to run the given program
-- when the initial heap is empty.

Maximum-heap-usage : Program ∞ → Conat ∞ → Set
Maximum-heap-usage p n = Least-upper-bound ∞ (⟦ p ⟧ 0) n

-- The smallest extra heap size that is required to run the given
-- program, for arbitrary initial heaps.

Maximum-heap-usage′ : Program ∞ → Conat ∞ → Set
Maximum-heap-usage′ p n =
  (∀ h → [ ∞ ] ⟦ p ⟧ h ⊑ n ⊕ ⌜ h ⌝)
    ×
  (∀ n′ → (∀ h → [ ∞ ] ⟦ p ⟧ h ⊑ n′ ⊕ ⌜ h ⌝) → [ ∞ ] n ≤ n′)

-- Maximum-heap-usage p n holds iff Maximum-heap-usage′ p n holds. For
-- this reason the former, less complicated definition will be used
-- below.

Maximum-heap-usage⇔Maximum-heap-usage′ :
  ∀ p n → Maximum-heap-usage p n ⇔ Maximum-heap-usage′ p n
Maximum-heap-usage⇔Maximum-heap-usage′ p n =
  ([ ∞ ] ⟦ p ⟧ 0 ⊑ n                  ↝⟨ ∀⟦⟧⊑⇔⟦⟧⊑ ⟩□
   (∀ h → [ ∞ ] ⟦ p ⟧ h ⊑ n ⊕ ⌜ h ⌝)  □)

    ×-cong

  ((∀ n′ → [ ∞ ] ⟦ p ⟧ 0 ⊑ n′ → [ ∞ ] n ≤ n′)                  ↝⟨ ∀-cong _ (λ _ → →-cong _ ∀⟦⟧⊑⇔⟦⟧⊑ F.id) ⟩□
   (∀ n′ → (∀ h → [ ∞ ] ⟦ p ⟧ h ⊑ n′ ⊕ ⌜ h ⌝) → [ ∞ ] n ≤ n′)  □)

-- The maximum heap usage is unique (up to bisimilarity).

max-unique :
  ∀ {p m n i} →
  Maximum-heap-usage p m → Maximum-heap-usage p n → Conat.[ i ] m ∼ n
max-unique = lub-unique

-- Maximum-heap-usage p respects bisimilarity.

max-respects-∼ :
  ∀ {p m n} →
  Conat.[ ∞ ] m ∼ n → Maximum-heap-usage p m → Maximum-heap-usage p n
max-respects-∼ {p} {m} {n} m∼n = Σ-map

  ([ ∞ ] ⟦ p ⟧ 0 ⊑ m  ↝⟨ (λ hyp → transitive-⊑≤ hyp (∼→≤ m∼n)) ⟩□
   [ ∞ ] ⟦ p ⟧ 0 ⊑ n  □)

  ((∀ o → [ ∞ ] ⟦ p ⟧ 0 ⊑ o → [ ∞ ] m ≤ o)  ↝⟨ (λ hyp₁ o hyp₂ → transitive-≤ (∼→≤ (Conat.symmetric-∼ m∼n)) (hyp₁ o hyp₂)) ⟩□
   (∀ o → [ ∞ ] ⟦ p ⟧ 0 ⊑ o → [ ∞ ] n ≤ o)  □ )

-- If the semantics of a program started in the empty heap does not
-- have a finite upper bound, then the maximum heap usage of the
-- program is infinity.

no-finite-max→infinite-max :
  ∀ p → (∀ n → ¬ [ ∞ ] ⟦ p ⟧ 0 ⊑ ⌜ n ⌝) →
  Maximum-heap-usage p infinity
no-finite-max→infinite-max p hyp =
    (⟦ p ⟧ 0 ⊑infinity)
  , λ n′ →
      [ ∞ ] ⟦ p ⟧ 0 ⊑ n′         ↝⟨ no-finite→infinite hyp ⟩
      Conat.[ ∞ ] n′ ∼ infinity  ↝⟨ ∼→≤ ∘ Conat.symmetric-∼ ⟩□
      [ ∞ ] infinity ≤ n′        □

-- If the maximum heap usage could always be determined, then WLPO
-- (which is a constructive taboo) would hold.

max→wlpo : (∀ p → ∃ λ n → Maximum-heap-usage p n) → WLPO
max→wlpo find-max = λ f → case find-max (p f) of λ where
    (zero  , max-0) → inj₁ (_⇔_.to 0⇔≡false max-0)
    (suc _ , max-+) → inj₂ (+→≢false max-+)
  where
  -- If f takes the value true, then p f contains exactly one
  -- occurrence of allocate, at the first index for which f takes the
  -- value true. Otherwise p f contains zero occurrences of allocate.

  p : ∀ {i} → (ℕ → Bool) → Program i
  p f = helper (f zero)
    module P where
    helper =
      if_then allocate   ∷ (λ { .force → repeat deallocate })
         else deallocate ∷ (λ { .force → p (f ∘ suc) })

  -- The maximum heap usage of p f is zero iff f always takes the
  -- value false.

  0⇔≡false :
    ∀ {f} → Maximum-heap-usage (p f) ⌜ 0 ⌝ ⇔ (∀ n → f n ≡ false)
  0⇔≡false = record
    { to   = →≡false _ ∘ proj₁
    ; from = λ ≡false →
          ≡false→ _ ≡false Nat.≤-refl
        , (λ _ _ → zero)
    }
    where
    →≡false : ∀ f → [ ∞ ] ⟦ p f ⟧ 0 ⊑ ⌜ 0 ⌝ → ∀ n → f n ≡ false
    →≡false f ⟦pf⟧0⊑0 _ = helper _ _ refl ⟦pf⟧0⊑0
      where
      helper : ∀ b n →
               f 0 ≡ b →
               [ ∞ ] ⟦ P.helper f b ⟧ 0 ⊑ ⌜ 0 ⌝ →
               f n ≡ false
      helper false zero    f0≡false = λ _ → f0≡false
      helper false (suc n) _        =
        [ ∞ ] ⟦ P.helper f false ⟧ 0 ⊑ ⌜ 0 ⌝  ↝⟨ □-tail ⟩
        [ ∞ ] ⟦ p (f ∘ suc)      ⟧ 0 ⊑ ⌜ 0 ⌝  ↝⟨ (λ hyp → →≡false (f ∘ suc) hyp n) ⟩□
        (f ∘ suc) n ≡ false                   □
      helper true n _ =
        [ ∞ ] ⟦ P.helper f true ⟧ 0 ⊑ ⌜ 0 ⌝  ↝⟨ □-head ∘ □-tail ⟩
        ([ ∞ ] ⌜ 1 ⌝ ≤ ⌜ 0 ⌝)                ↝⟨ ⌜⌝-mono⁻¹ ⟩
        1 ≤ 0                                ↝⟨ Nat.+≮ 0 ⟩
        ⊥                                    ↝⟨ ⊥-elim ⟩□
        f n ≡ false                          □

    ≡false→ :
      ∀ {m n i} f →
      (∀ n → f n ≡ false) →
      m ≤ n → [ i ] ⟦ p f ⟧ m ⊑ ⌜ n ⌝
    ≡false→ {m} {n} f ≡false m≤n with f 0 | ≡false 0
    ... | true  | ()
    ... | false | _  =
      zero +-mono ⌜⌝-mono m≤n ∷ λ { .force →
      ≡false→ (f ∘ suc) (≡false ∘ suc) (
        pred m  Nat.≤⟨ Nat.pred≤ _ ⟩
        m       Nat.≤⟨ m≤n ⟩∎
        n       ∎≤) }

  -- If the maximum heap usage of p f is positive, then f does not
  -- always take the value false.

  +→≢false :
    ∀ {f n} → Maximum-heap-usage (p f) (suc n) → ¬ (∀ n → f n ≡ false)
  +→≢false {f} {n} =
    Maximum-heap-usage (p f) (suc n)    ↝⟨ (λ max-+ →

        Maximum-heap-usage (p f) ⌜ 0 ⌝        ↝⟨ max-unique max-+ ⟩
        Conat.[ ∞ ] suc n ∼ ⌜ 0 ⌝             ↝⟨ (λ ()) ⟩□
        ⊥                                     □) ⟩

    ¬ Maximum-heap-usage (p f) ⌜ 0 ⌝    ↝⟨ (λ hyp ≡false → hyp (_⇔_.from 0⇔≡false ≡false)) ⟩□
    ¬ (∀ n → f n ≡ false)               □

-- Furthermore, if LPO holds, then the maximum heap usage can always
-- be determined.
--
-- TODO: I guess that LPO implies that least upper bounds can be
-- determined. Perhaps the proof below can be simplified.

lpo→max : LPO → (∀ p → ∃ λ n → Maximum-heap-usage p n)
lpo→max lpo =
  λ p → max-usage 0 p 0 , upper-bound 0 p 0 , least 0 p 0 Nat.≤-refl
  where
  -- The boolean next p h δ n is true if the n-th instruction
  -- (counting from zero) of p is the first one which forces the heap
  -- size to become strictly larger than δ + h, when the initial heap
  -- is h.

  next : Program ∞ → Heap → ℕ → ℕ → Bool
  next []               _       _       _       = false
  next (allocate   ∷ p) _       zero    zero    = true
  next (allocate   ∷ p) _       zero    (suc n) = false
  next (allocate   ∷ p) h       (suc δ) zero    = false
  next (allocate   ∷ p) h       (suc δ) (suc n) = next (force p) (suc h) δ n
  next (deallocate ∷ p) _       _       zero    = false
  next (deallocate ∷ p) zero    δ       (suc n) = next (force p) zero δ n
  next (deallocate ∷ p) (suc h) δ       (suc n) = next (force p) h (suc δ) n

  -- The number max-usage d p h is the maximum heap usage of ⟦ p ⟧ h,
  -- minus d (assuming that d ≤ h).

  max-usage : ∀ {i} → ℕ → Program ∞ → Heap → Conat i
  max-usage d = λ p h → case lpo (next p h 0) of λ where
      (inj₁ _)           → ⌜ h ∸ d ⌝
      (inj₂ (n , ≡true)) → step p h 0 n ≡true
    module M where
    step : ∀ {i} p h δ n → next p h δ n ≡ true → Conat i
    step []               _       _       _       ()
    step (allocate   ∷ p) h       zero    zero    _  = suc λ { .force →
                                                         max-usage (suc d) (force p) (suc h) }
    step (allocate   ∷ p) _       zero    (suc n) ()
    step (allocate   ∷ p) h       (suc δ) zero    ()
    step (allocate   ∷ p) h       (suc δ) (suc n)    = step (force p) (suc h) δ n
    step (deallocate ∷ p) _       _       zero    ()
    step (deallocate ∷ p) zero    δ       (suc n)    = step (force p) zero δ n
    step (deallocate ∷ p) (suc h) δ       (suc n)    = step (force p) h (suc δ) n

  -- Some simple lemmas.

  suc+∸∼+suc∸ :
    ∀ {m n} o → Conat.[ ∞ ] ⌜ suc m + n ∸ o ⌝ ∼ ⌜ m + suc n ∸ o ⌝
  suc+∸∼+suc∸ {m} o =
    ⌜⌝-cong (cong (_∸ o) (Nat.suc+≡+suc m))

  ∸suc≤→∸≤suc′ :
    ∀ {i m} n {o} →
    [ i ] ⌜ m ∸ suc n ⌝ ≤ force o → [ ssuc i ] ⌜ m ∸ n ⌝ ≤ suc o
  ∸suc≤→∸≤suc′ {i} {m} n {o} =
    [ i ] ⌜ m ∸ suc n ⌝ ≤ force o  ↝⟨ transitive-≤ (∼→≤ (Conat.symmetric-∼ (⌜⌝-∸ m (suc n)))) ⟩
    [ i ] ⌜ m ⌝ ⊖ suc n ≤ force o  ↝⟨ ∸suc≤→∸≤suc _ n ⟩
    [ ssuc i ] ⌜ m ⌝ ⊖ n ≤ suc o   ↝⟨ transitive-≤ (∼→≤ (⌜⌝-∸ _ n)) ⟩□
    [ ssuc i ] ⌜ m ∸ n ⌝ ≤ suc o   □

  ∸≤suc→∸suc≤′ :
    ∀ {m} n {o i} {j : Size< i} →
    [ i ] ⌜ m ∸ n ⌝ ≤ suc o → [ j ] ⌜ m ∸ suc n ⌝ ≤ force o
  ∸≤suc→∸suc≤′ {m} n {o} {i} {j} =
    [ i ] ⌜ m ∸ n ⌝ ≤ suc o        ↝⟨ transitive-≤ (∼→≤ (Conat.symmetric-∼ (⌜⌝-∸ _ n))) ⟩
    [ i ] ⌜ m ⌝ ⊖ n ≤ suc o        ↝⟨ ∸≤suc→∸suc≤ _ n ⟩
    [ j ] ⌜ m ⌝ ⊖ suc n ≤ force o  ↝⟨ transitive-≤ (∼→≤ (⌜⌝-∸ m (suc n))) ⟩□
    [ j ] ⌜ m ∸ suc n ⌝ ≤ force o  □

  ∸-cong : ∀ {m n} o → [ ∞ ] ⌜ m ⌝ ≤ ⌜ n ⌝ → [ ∞ ] ⌜ m ∸ o ⌝ ≤ ⌜ n ∸ o ⌝
  ∸-cong {m} {n} o =
    [ ∞ ] ⌜ m ⌝ ≤ ⌜ n ⌝          ↝⟨ ⌜⌝-mono⁻¹ ⟩
    (m ≤ n)                      ↝⟨ Nat._∸-mono Nat.≤-refl {n = o} ⟩
    (m ∸ o ≤ n ∸ o)              ↝⟨ ⌜⌝-mono ⟩□
    [ ∞ ] ⌜ m ∸ o ⌝ ≤ ⌜ n ∸ o ⌝  □

  module UB where

    mutual

      -- The value max-usage d p h is an upper bound of h minus d.

      upper-bound-≤ : ∀ {i} d p h → [ i ] ⌜ h ∸ d ⌝ ≤ max-usage d p h
      upper-bound-≤ d p h with lpo (next p h 0)
      ... | inj₁ _           = reflexive-≤ _
      ... | inj₂ (n , ≡true) = step d p h 0 n ≡true

      step : ∀ {i} d p h δ n (≡true : next p h δ n ≡ true) →
               [ i ] ⌜ δ + h ∸ d ⌝ ≤ M.step d p h δ n ≡true
      step d []               h       δ       zero    ()
      step d []               _       _       (suc n) ()
      step d (allocate   ∷ p) h       zero    zero    _     = transitive-≤ (⌜⌝-mono (Nat.pred≤ _))
                                                                (suc λ { .force →
                                                                   upper-bound-≤ (suc d) (force p) (suc h) })
      step d (allocate   ∷ p) _       zero    (suc n) ()
      step d (allocate   ∷ p) h       (suc δ) zero    ()
      step d (allocate   ∷ p) h       (suc δ) (suc n) ≡true = transitive-≤ (∼→≤ (suc+∸∼+suc∸ d))
                                                                (step d (force p) (suc h) δ n ≡true)
      step d (deallocate ∷ p) _       _       zero    ()
      step d (deallocate ∷ p) zero    δ       (suc n) ≡true = step d (force p) zero δ n ≡true
      step d (deallocate ∷ p) (suc h) δ       (suc n) ≡true = transitive-≤ (∼→≤ (Conat.symmetric-∼ (suc+∸∼+suc∸ d)))
                                                                  (step d (force p) h (suc δ) n ≡true)

  -- The value max-usage d p h is an upper bound of ⟦ p ⟧ h with d
  -- subtracted from every element.

  upper-bound :
    ∀ {i} d p h →
    □ i (λ h′ → [ ∞ ] ⌜ h′ ∸ d ⌝ ≤ max-usage d p h) (⟦ p ⟧ h)
  upper-bound d p h with lpo (next p h 0)
  ... | inj₁ ≡false = □-map (∸-cong d) (step p h 0 ≡false)
    where
    step : ∀ {i} p h δ (≡false : ∀ n → next p h δ n ≡ false) →
           [ i ] ⟦ p ⟧ h ⊑ ⌜ δ + h ⌝
    step []               h       δ       ≡false = ⌜⌝-mono (Nat.m≤n+m h δ) ∷ λ { .force → [] }
    step (allocate   ∷ p) h       zero    ≡false = ⊥-elim (Bool.true≢false (≡false 0))
    step (allocate   ∷ p) h       (suc δ) ≡false = ⌜⌝-mono (Nat.m≤n+m h (suc δ)) ∷ λ { .force →
                                                   transitive-⊑≤ (step (force p) (suc h) δ (≡false ∘ suc))
                                                                 (∼→≤ (⌜⌝-cong (sym (Nat.suc+≡+suc δ)))) }
    step (deallocate ∷ p) zero    δ       ≡false = zero ∷ λ { .force →
                                                   transitive-⊑≤ (step (force p) zero δ (≡false ∘ suc))
                                                                 (reflexive-≤ _) }
    step (deallocate ∷ p) (suc h) δ       ≡false = ⌜⌝-mono (Nat.m≤n+m (suc h) δ) ∷ λ { .force →
                                                   transitive-⊑≤ (step (force p) h (suc δ) (≡false ∘ suc))
                                                                 (∼→≤ (⌜⌝-cong (Nat.suc+≡+suc δ))) }

  ... | inj₂ (n , ≡true) = step _ p h 0 n ≡true
    where
    step : ∀ i p h δ n (≡true : next p h δ n ≡ true) →
           □ i (λ h′ → [ ∞ ] ⌜ h′ ∸ d ⌝ ≤ M.step d p h δ n ≡true)
               (⟦ p ⟧ h)
    step _ []               _       _       _       ()
    step _ (allocate   ∷ p) h       zero    zero    ≡true = UB.step d (allocate ∷ p) h zero zero ≡true
                                                            ∷ λ { .force → □-map (∸suc≤→∸≤suc′ d)
                                                                                 (upper-bound (suc d) (force p) (suc h)) }
    step _ (allocate   ∷ p) _       zero    (suc n) ()
    step _ (allocate   ∷ p) h       (suc δ) zero    ()
    step _ (allocate   ∷ p) h       (suc δ) (suc n) ≡true = transitive-≤
                                                              (⌜⌝-mono (Nat.zero≤ δ Nat.+-mono Nat.pred≤ _ Nat.∸-mono Nat.≤-refl {n = d}))
                                                              (UB.step d (force p) (suc h) δ n ≡true)
                                                            ∷ λ { .force → step _ (force p) (suc h) δ n ≡true }
    step _ (deallocate ∷ p) _       _       zero    ()
    step i (deallocate ∷ p) zero    δ       (suc n) ≡true = □-head (step i (force p) zero δ n ≡true)
                                                            ∷ λ { .force → step _ (force p) zero δ n ≡true }
    step _ (deallocate ∷ p) (suc h) δ       (suc n) ≡true = transitive-≤
                                                              (⌜⌝-mono (Nat.m≤m+n 1 δ Nat.+-mono Nat.≤-refl Nat.∸-mono Nat.≤-refl {n = d}))
                                                              (UB.step d (force p) h (suc δ) n ≡true)
                                                            ∷ λ { .force → step _ (force p) h (suc δ) n ≡true }

  -- The value max-usage d p h is below every number that is an upper
  -- bound of ⟦ p ⟧ h with d subtracted from every element.

  least :
    ∀ {i} d p h → d ≤ h →
    ∀ m → □ ∞ (λ h′ → [ ∞ ] ⌜ h′ ∸ d ⌝ ≤ m) (⟦ p ⟧ h) →
    [ i ] max-usage d p h ≤ m
  least d p h d≤h m with lpo (next p h 0)
  ... | inj₁ _           = □-head
  ... | inj₂ (n , ≡true) = step p h 0 n ≡true d≤h m
    where
    step : ∀ {i} p h δ n (≡true : next p h δ n ≡ true) →
           d ≤ δ + h →
           ∀ m → □ ∞ (λ h′ → [ ∞ ] ⌜ h′ ∸ d ⌝ ≤ m) (⟦ p ⟧ h) →
           [ i ] M.step d p h δ n ≡true ≤ m
    step []               _       _       _       ()
    step (allocate   ∷ p) h       zero    zero    ≡true d≤ zero    ⊑0   = ⊥-elim (Nat.≮0 _ (
                                                                            suc (h ∸ d)  Nat.≡⟨ sym (Nat.+-∸-assoc d≤) ⟩≤
                                                                            suc h ∸ d    Nat.≤⟨ ⌜⌝-mono⁻¹ (□-head (□-tail ⊑0)) ⟩∎
                                                                            zero         ∎≤))
    step (allocate   ∷ p) h       zero    zero    ≡true d≤ (suc m) ⊑1+m = suc λ { .force →
                                                                            least (suc d) (force p) (suc h) (Nat.suc≤suc d≤) (force m)
                                                                                  (□-map (∸≤suc→∸suc≤′ d) (□-tail ⊑1+m)) }
    step (allocate   ∷ p) _       zero    (suc n) ()
    step (allocate   ∷ p) h       (suc δ) zero    ()
    step (allocate   ∷ p) h       (suc δ) (suc n) ≡true d≤ m       = step (force p) (suc h) δ n ≡true (d            Nat.≤⟨ d≤ ⟩
                                                                                                       suc (δ + h)  Nat.≡⟨ Nat.suc+≡+suc _ ⟩≤
                                                                                                       δ + suc h    Nat.∎≤) m ∘
                                                                     □-tail
    step (deallocate ∷ p) _       _       zero    ()
    step (deallocate ∷ p) zero    δ       (suc n) ≡true d≤ m       = step (force p) zero δ n ≡true d≤ m ∘ □-tail
    step (deallocate ∷ p) (suc h) δ       (suc n) ≡true d≤ m       = step (force p) h (suc δ) n ≡true (d            Nat.≤⟨ d≤ ⟩
                                                                                                       δ + suc h    Nat.≡⟨ sym (Nat.suc+≡+suc _) ⟩≤
                                                                                                       suc (δ + h)  Nat.∎≤) m ∘
                                                                     □-tail

------------------------------------------------------------------------
-- Some examples

open Bounded-space public
  using (constant-space; constant-space₂; unbounded-space)

-- Zero is not an upper bound of the semantics of constant-space when
-- it is started with an empty heap.

⟦constant-space⟧⋢0 : ¬ [ ∞ ] ⟦ constant-space ⟧ 0 ⊑ ⌜ 0 ⌝
⟦constant-space⟧⋢0 =
  [ ∞ ] ⟦ constant-space ⟧ 0 ⊑ ⌜ 0 ⌝  ↝⟨ □-head ∘ □-tail ⟩
  [ ∞ ] ⌜ 1 ⌝ ≤ ⌜ 0 ⌝                 ↝⟨ ⌜⌝-mono⁻¹ ⟩
  (1 ≤ 0)                             ↝⟨ Nat.+≮ 0 ⟩□
  ⊥                                   □

-- However, one is.

⟦constant-space⟧⊑1 :
  ∀ {i} → [ i ] ⟦ constant-space ⟧ 0 ⊑ ⌜ 1 ⌝
⟦constant-space⟧⊑1 =
  ≤suc          ∷ λ { .force →
  reflexive-≤ _ ∷ λ { .force →
  ⟦constant-space⟧⊑1 }}

-- The maximum heap usage of constant-space is 1.

max-constant-space-1 : Maximum-heap-usage constant-space ⌜ 1 ⌝
max-constant-space-1 =
    ⟦constant-space⟧⊑1
  , λ n′ →
      [ ∞ ] ⟦ constant-space ⟧ 0 ⊑ n′  ↝⟨ □-head ∘ □-tail ⟩□
      [ ∞ ] ⌜ 1 ⌝ ≤ n′                 □

-- Two is an upper bound of the semantics of constant-space₂ when it
-- is started in an empty heap.

⟦constant-space₂⟧⊑2 :
  ∀ {i} → [ i ] ⟦ constant-space₂ ⟧ 0 ⊑ ⌜ 2 ⌝
⟦constant-space₂⟧⊑2 =
  zero                      ∷ λ { .force →
  suc (λ { .force → zero }) ∷ λ { .force →
  reflexive-≤ _             ∷ λ { .force →
  suc (λ { .force → zero }) ∷ λ { .force →
  ⟦constant-space₂⟧⊑2 }}}}

-- The maximum heap usage of constant-space₂ is 2.

max-constant-space₂-2 : Maximum-heap-usage constant-space₂ ⌜ 2 ⌝
max-constant-space₂-2 =
    ⟦constant-space₂⟧⊑2
  , λ n′ →
    [ ∞ ] ⟦ constant-space₂ ⟧ 0 ⊑ n′  ↝⟨ □-head ∘ □-tail ∘ □-tail ⟩□
    [ ∞ ] ⌜ 2 ⌝ ≤ n′                  □

-- There is no finite upper bound of the semantics of unbounded-space.

⟦unbounded-space⟧⋢⌜⌝ :
  ∀ {n} → ¬ [ ∞ ] ⟦ unbounded-space ⟧ 0 ⊑ ⌜ n ⌝
⟦unbounded-space⟧⋢⌜⌝ {n} = helper (Nat.≤→≤↑ (Nat.zero≤ _))
  where
  helper :
    ∀ {h} → h ≤↑ 1 + n → ¬ [ ∞ ] ⟦ unbounded-space ⟧ h ⊑ ⌜ n ⌝
  helper (Nat.≤↑-refl refl) =
    [ ∞ ] ⟦ unbounded-space ⟧ (1 + n) ⊑ ⌜ n ⌝  ↝⟨ □-head ⟩
    [ ∞ ] ⌜ 1 + n ⌝ ≤ ⌜ n ⌝                    ↝⟨ ⌜⌝-mono⁻¹ ⟩
    (1 + n ≤ n)                                ↝⟨ Nat.+≮ 0 ⟩□
    ⊥                                          □
  helper {h} (Nat.≤↑-step 1+h≤1+n) =
    [ ∞ ] ⟦ unbounded-space ⟧ h ⊑ ⌜ n ⌝        ↝⟨ □-tail ⟩
    [ ∞ ] ⟦ unbounded-space ⟧ (1 + h) ⊑ ⌜ n ⌝  ↝⟨ helper 1+h≤1+n ⟩□
    ⊥                                          □

-- The maximum heap usage of unbounded-space is infinity.

max-unbounded-space-∞ : Maximum-heap-usage unbounded-space infinity
max-unbounded-space-∞ =
  no-finite-max→infinite-max unbounded-space λ _ → ⟦unbounded-space⟧⋢⌜⌝

------------------------------------------------------------------------
-- A relation that can be used to relate the least upper bounds of two
-- colists

-- [ ∞ ] ms ≲ ns implies that the least upper bound of ms is less than
-- or equal to that of ns (see ≲→least-upper-bounds-≤ below).

infix 4 [_]_≲_ [_]_≲′_

[_]_≲_ : Size → Colist ℕ ∞ → Colist ℕ ∞ → Set
[ i ] ms ≲ ns = □ i (λ m → ◇ (m ≤_) ns) ms

[_]_≲′_ : Size → Colist ℕ ∞ → Colist ℕ ∞ → Set
[ i ] ms ≲′ ns = □′ i (λ m → ◇ (m ≤_) ns) ms

-- Some derived cons-like operations.

consʳ : ∀ {ms ns n i} →
        [ i ] ms ≲ force ns →
        [ i ] ms ≲ n ∷ ns
consʳ = □-map there

cons : ∀ {i m ms n ns} →
       m ≤ n →
       [ i ] force ms ≲′ force ns →
       [ i ] m ∷ ms ≲ n ∷ ns
cons p q = here p ∷ λ { .force → consʳ (force q) }

cons′ : ∀ {i m ms ns} →
        [ i ] force ms ≲′ force ns →
        [ i ] m ∷ ms ≲ m ∷ ns
cons′ = cons Nat.≤-refl

-- "Equational" reasoning combinators.

infix  -1 _□≲
infixr -2 step-≲ step-≡≲ _≡⟨⟩≲_ step-∼≲

step-≲ : ∀ {i} ms {ns os} →
         [ ∞ ] ns ≲ os → [ i ] ms ≲ ns → [ i ] ms ≲ os
step-≲ _ ns≲os ms≲ns = □-map (lemma ns≲os) ms≲ns
  where
  lemma :
    ∀ {m ms ns} →
    [ ∞ ] ms ≲ ns →
    ◇ (m ≤_) ms → ◇ (m ≤_) ns
  lemma (p ∷ _) (here m≤) = ◇-map (Nat.≤-trans m≤) p
  lemma (_ ∷ p) (there q) = lemma (force p) q

syntax step-≲ ms ns≲os ms≲ns = ms ≲⟨ ms≲ns ⟩ ns≲os

step-≡≲ : ∀ {i} ms {ns os} → [ i ] ns ≲ os → ms ≡ ns → [ i ] ms ≲ os
step-≡≲ _ ns≲os refl = ns≲os

syntax step-≡≲ ms ns≲os ms≡ns = ms ≡⟨ ms≡ns ⟩≲ ns≲os

_≡⟨⟩≲_ : ∀ {i} ms {ns} → [ i ] ms ≲ ns → [ i ] ms ≲ ns
_ ≡⟨⟩≲ ms≲ns = ms≲ns

step-∼≲ : ∀ {i} ms {ns os} →
          [ i ] ns ≲ os → Colist.[ i ] ms ∼ ns → [ i ] ms ≲ os
step-∼≲ _ ns≲os ms∼ns = □-∼ (Colist.symmetric-∼ ms∼ns) ns≲os

syntax step-∼≲ ms ns≲os ms∼ns = ms ∼⟨ ms∼ns ⟩≲ ns≲os

_□≲ : ∀ {i} ns → [ i ] ns ≲ ns
[]     □≲ = []
n ∷ ns □≲ = cons′ λ { .force → force ns □≲ }

-- If [ ∞ ] ms ≲ ns, then any least upper bound of ms is less than or
-- equal to any least upper bound of ns.
--
-- TODO: Figure out what the status is of the converse statement.

≲→least-upper-bounds-≤ :
  ∀ {m n ms ns} →
  [ ∞ ] ms ≲ ns →
  Least-upper-bound ∞ ms m →
  Least-upper-bound ∞ ns n →
  [ ∞ ] m ≤ n
≲→least-upper-bounds-≤ {m} {n} {ms} {ns} ms≲ns m-lub =
  Least-upper-bound ∞ ns n                 ↝⟨ proj₁ ⟩
  [ ∞ ] ns ⊑ n                             ↝⟨ (λ hyp → flip transitive-◇≤⊑ hyp) ⟩
  (∀ {m} → ◇ (m ≤_) ns → [ ∞ ] ⌜ m ⌝ ≤ n)  ↝⟨ (λ hyp → □-map hyp ms≲ns) ⟩
  [ ∞ ] ms ⊑ n                             ↝⟨ proj₂ m-lub _ ⟩□
  [ ∞ ] m ≤ n                              □

------------------------------------------------------------------------
-- A simple optimiser

-- An optimiser that replaces subsequences of the form "allocate,
-- allocate, deallocate" with "allocate".

optimise : ∀ {i} → Program ∞ → Program i
optimise []               = []
optimise (deallocate ∷ p) = deallocate ∷ λ { .force →
                              optimise (force p) }
optimise (allocate   ∷ p) = optimise₁ (force p)
  module Optimise where
  default : ∀ {i} → Program i
  default = allocate ∷ λ { .force → optimise (force p) }

  optimise₂ : ∀ {i} → Program ∞ → Program i
  optimise₂ (deallocate ∷ p″) = allocate ∷ λ { .force →
                                  optimise (force p″) }
  optimise₂ _                 = default

  optimise₁ : ∀ {i} → Program ∞ → Program i
  optimise₁ (allocate ∷ p′) = optimise₂ (force p′)
  optimise₁ _               = default

-- The optimised program's maximum heap usage is at most as large as
-- that of the original program.

mutual

  optimise-correct :
    ∀ {i m n} p →
    Maximum-heap-usage (optimise p) m →
    Maximum-heap-usage p n →
    [ i ] m ≤ n
  optimise-correct = ≲→least-upper-bounds-≤ ∘ optimise-correct-≲

  optimise-correct-≲ : ∀ {h i} p → [ i ] ⟦ optimise p ⟧ h ≲ ⟦ p ⟧ h
  optimise-correct-≲ {h} [] =
    ⟦ optimise [] ⟧ h  ∼⟨ ∷∼∷′ ⟩≲
    h ∷′ []            ∼⟨ Colist.symmetric-∼ ∷∼∷′ ⟩≲
    ⟦ [] ⟧ h           □≲

  optimise-correct-≲ {h} (deallocate ∷ p) =
    ⟦ optimise (deallocate ∷ p) ⟧ h       ∼⟨ ∷∼∷′ ⟩≲
    h ∷′ ⟦ optimise (force p) ⟧ (pred h)  ≲⟨ (cons′ λ { .force → optimise-correct-≲ (force p) }) ⟩
    h ∷′ ⟦ force p ⟧ (pred h)             ∼⟨ Colist.symmetric-∼ ∷∼∷′ ⟩≲
    ⟦ deallocate ∷ p ⟧ h                  □≲

  optimise-correct-≲ {h} (allocate ∷ p) =
    ⟦ optimise (allocate ∷ p) ⟧ h         ≡⟨⟩≲
    ⟦ Optimise.optimise₁ p (force p) ⟧ h  ≲⟨ optimise-correct₁ _ refl ⟩
    h ∷′ ⟦ force p ⟧ (1 + h)              ∼⟨ Colist.symmetric-∼ ∷∼∷′ ⟩≲
    ⟦ allocate ∷ p ⟧ h                    □≲
    where
    default-correct :
      ∀ {p′ i} →
      p′ ≡ force p →
      [ i ] ⟦ Optimise.default p ⟧ h ≲ h ∷′ ⟦ p′ ⟧ (1 + h)
    default-correct refl =
      ⟦ Optimise.default p ⟧ h             ∼⟨ ∷∼∷′ ⟩≲
      h ∷′ ⟦ optimise (force p) ⟧ (1 + h)  ≲⟨ (cons′ λ { .force → optimise-correct-≲ (force p) }) ⟩
      h ∷′ ⟦ force p ⟧ (1 + h)             □≲

    optimise-correct₁ :
      ∀ {i} p′ →
      p′ ≡ force p →
      [ i ] ⟦ Optimise.optimise₁ p p′ ⟧ h ≲ h ∷′ ⟦ p′ ⟧ (1 + h)
    optimise-correct₁ []                []≡ = default-correct []≡
    optimise-correct₁ (deallocate ∷ p′) d∷≡ = default-correct d∷≡
    optimise-correct₁ (allocate   ∷ p′) a∷≡ = optimise-correct₂ _ refl
      where
      optimise-correct₂ :
        ∀ {i} p″ →
        p″ ≡ force p′ →
        [ i ] ⟦ Optimise.optimise₂ p p″ ⟧ h ≲
              h ∷′ ⟦ allocate ∷ p′ ⟧ (1 + h)
      optimise-correct₂ []                _   = default-correct a∷≡
      optimise-correct₂ (allocate   ∷ p″) _   = default-correct a∷≡
      optimise-correct₂ (deallocate ∷ p″) d∷≡ =
        ⟦ Optimise.optimise₂ p (deallocate ∷ p″) ⟧ h  ∼⟨ ∷∼∷′ ⟩≲
        h ∷′ ⟦ optimise (force p″) ⟧ (1 + h)          ≲⟨ (cons′ λ { .force → consʳ (consʳ (optimise-correct-≲ (force p″))) }) ⟩
        h ∷′ 1 + h ∷′ 2 + h ∷′ ⟦ force p″ ⟧ (1 + h)   ∼⟨ (refl ∷ λ { .force → refl ∷ λ { .force → Colist.symmetric-∼ ∷∼∷′ } }) ⟩≲
        h ∷′ 1 + h ∷′ ⟦ deallocate ∷ p″ ⟧ (2 + h)     ≡⟨ by d∷≡ ⟩≲
        h ∷′ 1 + h ∷′ ⟦ force p′ ⟧ (2 + h)            ∼⟨ (refl ∷ λ { .force → Colist.symmetric-∼ ∷∼∷′ }) ⟩≲
        h ∷′ ⟦ allocate ∷ p′ ⟧ (1 + h)                □≲
