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
open import Conat hiding (pred) renaming (_+_ to _⊕_)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Omniscience
open import Prelude
open import Tactic.By

open import Function-universe equality-with-J as F hiding (_∘_)
open import Nat equality-with-J as Nat using (_≤_; _≤↑_; pred)

open import Only-allocation
open import Upper-bounds

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
-- The maximum heap usage predicate

-- The smallest heap size that is required to run the given program
-- when the initial heap is empty.

Maximum-heap-usage : Program ∞ → Conat ∞ → Set
Maximum-heap-usage p n = Least-upper-bound (⟦ p ⟧ 0) n

-- The smallest extra heap size that is required to run the given
-- program, for arbitrary initial heaps.

Maximum-heap-usage′ : Program ∞ → Conat ∞ → Set
Maximum-heap-usage′ p n =
  (∀ h → [ ∞ ] ⟦ p ⟧ h ⊑ n ⊕ ⌜ h ⌝)
    ×
  (∀ n′ → (∀ h → [ ∞ ] ⟦ p ⟧ h ⊑ n′ ⊕ ⌜ h ⌝) → [ ∞ ] n ≤ n′)

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
  ∀ {p q m n} →
  Colist.[ ∞ ] ⟦ p ⟧ 0 ∼ ⟦ q ⟧ 0 →
  Conat.[ ∞ ] m ∼ n →
  Maximum-heap-usage p m → Maximum-heap-usage q n
max-respects-∼ {p} {q} {m} {n} p∼q m∼n = Σ-map

  ([ ∞ ] ⟦ p ⟧ 0 ⊑ m  ↝⟨ (λ hyp → transitive-⊑≤ (□-∼ p∼q hyp) (∼→≤ m∼n)) ⟩□
   [ ∞ ] ⟦ q ⟧ 0 ⊑ n  □)

  ((∀ o → [ ∞ ] ⟦ p ⟧ 0 ⊑ o → [ ∞ ] m ≤ o)  ↝⟨ (λ hyp₁ o hyp₂ → transitive-≤ (∼→≤ (Conat.symmetric-∼ m∼n))
                                                                             (hyp₁ o (□-∼ (Colist.symmetric-∼ p∼q) hyp₂))) ⟩□
   (∀ o → [ ∞ ] ⟦ q ⟧ 0 ⊑ o → [ ∞ ] n ≤ o)  □)

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

-- If the maximum heap usage could always be determined (in a certain
-- sense), then WLPO (which is a constructive taboo) would hold.

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

-- In fact, WLPO is logically equivalent to a certain formulation of
-- "the maximum heap usage can always be determined".

wlpo⇔max : WLPO ⇔ (∀ p → ∃ λ n → Maximum-heap-usage p n)
wlpo⇔max = record
  { to   = λ wlpo p → wlpo→lub wlpo (⟦ p ⟧ 0)
  ; from = max→wlpo
  }

-- We also get that WLPO is logically equivalent to a certain
-- formulation of "least upper bounds of colists of natural numbers
-- can always be determined".

wlpo⇔lub : WLPO ⇔ (∀ ms → ∃ λ n → Least-upper-bound ms n)
wlpo⇔lub = record
  { to   = wlpo→lub
  ; from = λ find-lub → max→wlpo (λ p → find-lub (⟦ p ⟧ 0))
  }

------------------------------------------------------------------------
-- Some examples

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
  optimise-correct p max₁ max₂ =
    _⇔_.to (≲⇔least-upper-bounds-≤ max₁ max₂) (optimise-correct-≲ p)

  optimise-correct-≲ : ∀ {h i} p → [ i ] ⟦ optimise p ⟧ h ≲ ⟦ p ⟧ h
  optimise-correct-≲ {h} [] =
    ⟦ optimise [] ⟧ h  ∼⟨ ∷∼∷′ ⟩≲
    h ∷′ []            ∼⟨ Colist.symmetric-∼ ∷∼∷′ ⟩≲
    ⟦ [] ⟧ h           □≲

  optimise-correct-≲ {h} (deallocate ∷ p) =
    ⟦ optimise (deallocate ∷ p) ⟧ h       ∼⟨ ∷∼∷′ ⟩≲
    h ∷′ ⟦ optimise (force p) ⟧ (pred h)  ≲⟨ ⌊ cons′-≲D (λ { .force → ⌈ optimise-correct-≲ (force p) ⌉ }) ⌋≲ ⟩
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
      h ∷′ ⟦ optimise (force p) ⟧ (1 + h)  ≲⟨ (cons′-≲ λ { hyp .force → optimise-correct-≲ (force p) hyp }) ⟩
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
        h ∷′ ⟦ optimise (force p″) ⟧ (1 + h)          ≲⟨ ⌊ cons′-≲D (λ { .force → ⌈ consʳ-≲ (consʳ-≲ (optimise-correct-≲ (force p″))) ⌉ }) ⌋≲ ⟩
        h ∷′ 1 + h ∷′ 2 + h ∷′ ⟦ force p″ ⟧ (1 + h)   ∼⟨ (refl ∷ λ { .force → refl ∷ λ { .force → Colist.symmetric-∼ ∷∼∷′ } }) ⟩≲
        h ∷′ 1 + h ∷′ ⟦ deallocate ∷ p″ ⟧ (2 + h)     ≡⟨ by d∷≡ ⟩≲
        h ∷′ 1 + h ∷′ ⟦ force p′ ⟧ (2 + h)            ∼⟨ (refl ∷ λ { .force → Colist.symmetric-∼ ∷∼∷′ }) ⟩≲
        h ∷′ ⟦ allocate ∷ p′ ⟧ (1 + h)                □≲

-- Sometimes the optimised program's maximum heap usage is less than
-- that of the original program.

optimise-improves :
  ∃ λ p →
    Maximum-heap-usage p ⌜ 2 ⌝ ×
    Maximum-heap-usage (optimise p) ⌜ 1 ⌝
optimise-improves =
    constant-space₂
  , max-constant-space₂-2
  , max-respects-∼ lemma (_ ∎∼) max-constant-space-1
  where

  lemma :
    ∀ {i} →
    Colist.[ i ] ⟦ constant-space ⟧ 0 ∼ ⟦ optimise constant-space₂ ⟧ 0
  lemma =
    refl ∷ λ { .force →
    refl ∷ λ { .force →
    lemma }}
