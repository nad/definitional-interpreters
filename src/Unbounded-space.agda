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

{-# OPTIONS --without-K --safe --sized-types #-}

module Unbounded-space where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Tactic.By.Propositional
open import Prelude.Size

open import Colist equality-with-J as Colist
open import Conat equality-with-J as Conat
  hiding (pred) renaming (_+_ to _⊕_)
open import Function-universe equality-with-J as F hiding (_∘_)
open import Nat equality-with-J as Nat using (_≤_; _≤↑_; pred)
open import Omniscience equality-with-J

open import Only-allocation
open import Upper-bounds

------------------------------------------------------------------------
-- Definitional interpreter

-- Modifies the heap size according to the given instruction.

modify : Stmt → ℕ → ℕ
modify alloc   = suc
modify dealloc = pred

-- A definitional interpreter. It returns a trace of all heap sizes
-- encountered during the program's run. The input is the initial heap
-- size.

mutual

  ⟦_⟧ : ∀ {i} → Program i → ℕ → Colist ℕ i
  ⟦ p ⟧ h = h ∷ ⟦ p ⟧′ h

  ⟦_⟧′ : ∀ {i} → Program i → ℕ → Colist′ ℕ i
  ⟦ []    ⟧′ h .force = []
  ⟦ s ∷ p ⟧′ h .force = ⟦ p .force ⟧ (modify s h)

------------------------------------------------------------------------
-- The maximum heap usage predicate

-- The smallest heap size that is required to run the given program
-- when the initial heap is empty.

Heap-usage : Program ∞ → Conat ∞ → Set
Heap-usage p n = LUB (⟦ p ⟧ 0) n

-- The smallest extra heap size that is required to run the given
-- program, for arbitrary initial heaps.

Heap-usage′ : Program ∞ → Conat ∞ → Set
Heap-usage′ p n =
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
    to′ _       alloc   p⊑ = to (force p) p⊑ h
    to′ (suc m) dealloc p⊑ = to (force p) p⊑ h
    to′ zero    dealloc p⊑ = transitive-⊑≤ (to (force p) p⊑ (pred h))
                                           (reflexive-≤ n
                                              +-mono
                                            ⌜⌝-mono (Nat.pred≤ _))

-- Heap-usage p n holds iff Heap-usage′ p n holds. For this reason the
-- former, less complicated definition will be used below.

Heap-usage⇔Heap-usage′ :
  ∀ p n → Heap-usage p n ⇔ Heap-usage′ p n
Heap-usage⇔Heap-usage′ p n =
  ([ ∞ ] ⟦ p ⟧ 0 ⊑ n                  ↝⟨ ∀⟦⟧⊑⇔⟦⟧⊑ ⟩□
   (∀ h → [ ∞ ] ⟦ p ⟧ h ⊑ n ⊕ ⌜ h ⌝)  □)

    ×-cong

  ((∀ n′ → [ ∞ ] ⟦ p ⟧ 0 ⊑ n′ → [ ∞ ] n ≤ n′)                  ↝⟨ ∀-cong _ (λ _ → →-cong _ ∀⟦⟧⊑⇔⟦⟧⊑ F.id) ⟩□
   (∀ n′ → (∀ h → [ ∞ ] ⟦ p ⟧ h ⊑ n′ ⊕ ⌜ h ⌝) → [ ∞ ] n ≤ n′)  □)

-- The maximum heap usage is unique (up to bisimilarity).

max-unique :
  ∀ {p m n i} →
  Heap-usage p m → Heap-usage p n → Conat.[ i ] m ∼ n
max-unique = lub-unique

-- Heap-usage p respects bisimilarity.

max-respects-∼ :
  ∀ {p q m n} →
  Colist.[ ∞ ] ⟦ p ⟧ 0 ∼ ⟦ q ⟧ 0 →
  Conat.[ ∞ ] m ∼ n →
  Heap-usage p m → Heap-usage q n
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
  ∀ p → (∀ n → ¬ [ ∞ ] ⟦ p ⟧ 0 ⊑ ⌜ n ⌝) → Heap-usage p infinity
no-finite-max→infinite-max p hyp =
    (⟦ p ⟧ 0 ⊑infinity)
  , λ n′ →
      [ ∞ ] ⟦ p ⟧ 0 ⊑ n′         ↝⟨ no-finite→infinite hyp ⟩
      Conat.[ ∞ ] n′ ∼ infinity  ↝⟨ ∼→≤ ∘ Conat.symmetric-∼ ⟩□
      [ ∞ ] infinity ≤ n′        □

-- If the maximum heap usage could always be determined (in a certain
-- sense), then WLPO (which is a constructive taboo) would hold.

max→wlpo : (∀ p → ∃ λ n → Heap-usage p n) → WLPO
max→wlpo find-max = λ f → case find-max (p f) of λ where
    (zero  , max-0) → inj₁ (_⇔_.to 0⇔≡false max-0)
    (suc _ , max-+) → inj₂ (+→≢false max-+)
  where
  -- If f takes the value true, then p f contains exactly one
  -- occurrence of alloc, at the first index for which f takes the
  -- value true. Otherwise p f contains zero occurrences of alloc.

  p : ∀ {i} → (ℕ → Bool) → Program i
  p f = helper (f 0)
    module P where
    helper : ∀ {i} → Bool → Program i
    helper =
      if_then alloc   ∷′ []
         else dealloc ∷  λ { .force → p (λ n → f (1 + n)) }

  -- The maximum heap usage of p f is zero iff f always takes the
  -- value false.

  0⇔≡false :
    ∀ {f} → Heap-usage (p f) ⌜ 0 ⌝ ⇔ (∀ n → f n ≡ false)
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
    ∀ {f n} → Heap-usage (p f) (suc n) → ¬ (∀ n → f n ≡ false)
  +→≢false {f} {n} =
    Heap-usage (p f) (suc n)     ↝⟨ (λ max-+ →

      Heap-usage (p f) ⌜ 0 ⌝           ↝⟨ max-unique max-+ ⟩
      Conat.[ ∞ ] suc n ∼ ⌜ 0 ⌝        ↝⟨ (λ ()) ⟩□
      ⊥                                □) ⟩

    ¬ Heap-usage (p f) ⌜ 0 ⌝     ↝⟨ (λ hyp ≡false → hyp (_⇔_.from 0⇔≡false ≡false)) ⟩□
    ¬ (∀ n → f n ≡ false)        □

-- In fact, WLPO is logically equivalent to a certain formulation of
-- "the maximum heap usage can always be determined".

wlpo⇔max : WLPO ⇔ (∀ p → ∃ λ n → Heap-usage p n)
wlpo⇔max = record
  { to   = λ wlpo p → wlpo→lub wlpo (⟦ p ⟧ 0)
  ; from = max→wlpo
  }

-- We also get that WLPO is logically equivalent to a certain
-- formulation of "least upper bounds of colists of natural numbers
-- can always be determined".

wlpo⇔lub : WLPO ⇔ (∀ ms → ∃ λ n → LUB ms n)
wlpo⇔lub = record
  { to   = wlpo→lub
  ; from = λ find-lub → max→wlpo (λ p → find-lub (⟦ p ⟧ 0))
  }

------------------------------------------------------------------------
-- Some examples

-- When this semantics is used all three programs are non-terminating,
-- in the sense that their traces are infinitely long.

bounded-loops :
  ∀ {i n} → Conat.[ i ] length (⟦ bounded ⟧ n) ∼ infinity
bounded-loops =
  suc λ { .force →
  suc λ { .force →
  bounded-loops }}

bounded₂-loops :
  ∀ {i n} → Conat.[ i ] length (⟦ bounded₂ ⟧ n) ∼ infinity
bounded₂-loops =
  suc λ { .force →
  suc λ { .force →
  suc λ { .force →
  suc λ { .force →
  bounded₂-loops }}}}

unbounded-loops :
  ∀ {i n} → Conat.[ i ] length (⟦ unbounded ⟧ n) ∼ infinity
unbounded-loops =
  suc λ { .force →
  unbounded-loops }

-- Zero is not an upper bound of the semantics of bounded when it is
-- started with an empty heap.

⟦bounded⟧⋢0 : ¬ [ ∞ ] ⟦ bounded ⟧ 0 ⊑ ⌜ 0 ⌝
⟦bounded⟧⋢0 =
  [ ∞ ] ⟦ bounded ⟧ 0 ⊑ ⌜ 0 ⌝  ↝⟨ □-head ∘ □-tail ⟩
  [ ∞ ] ⌜ 1 ⌝ ≤ ⌜ 0 ⌝          ↝⟨ ⌜⌝-mono⁻¹ ⟩
  (1 ≤ 0)                      ↝⟨ Nat.+≮ 0 ⟩□
  ⊥                            □

-- However, one is.

⟦bounded⟧⊑1 :
  ∀ {i} → [ i ] ⟦ bounded ⟧ 0 ⊑ ⌜ 1 ⌝
⟦bounded⟧⊑1 =
  ≤suc          ∷ λ { .force →
  reflexive-≤ _ ∷ λ { .force →
  ⟦bounded⟧⊑1 }}

-- The maximum heap usage of bounded is 1.

max-bounded-1 : Heap-usage bounded ⌜ 1 ⌝
max-bounded-1 =
    ⟦bounded⟧⊑1
  , λ n′ →
      [ ∞ ] ⟦ bounded ⟧ 0 ⊑ n′  ↝⟨ □-head ∘ □-tail ⟩□
      [ ∞ ] ⌜ 1 ⌝ ≤ n′          □

-- Two is an upper bound of the semantics of bounded₂ when it is
-- started in an empty heap.

⟦bounded₂⟧⊑2 :
  ∀ {i} → [ i ] ⟦ bounded₂ ⟧ 0 ⊑ ⌜ 2 ⌝
⟦bounded₂⟧⊑2 =
  zero                      ∷ λ { .force →
  suc (λ { .force → zero }) ∷ λ { .force →
  reflexive-≤ _             ∷ λ { .force →
  suc (λ { .force → zero }) ∷ λ { .force →
  ⟦bounded₂⟧⊑2 }}}}

-- The maximum heap usage of bounded₂ is 2.

max-bounded₂-2 : Heap-usage bounded₂ ⌜ 2 ⌝
max-bounded₂-2 =
    ⟦bounded₂⟧⊑2
  , λ n′ →
    [ ∞ ] ⟦ bounded₂ ⟧ 0 ⊑ n′  ↝⟨ □-head ∘ □-tail ∘ □-tail ⟩□
    [ ∞ ] ⌜ 2 ⌝ ≤ n′           □

-- There is no finite upper bound of the semantics of unbounded.

⟦unbounded⟧⋢⌜⌝ :
  ∀ {n} → ¬ [ ∞ ] ⟦ unbounded ⟧ 0 ⊑ ⌜ n ⌝
⟦unbounded⟧⋢⌜⌝ {n} = helper (Nat.≤→≤↑ (Nat.zero≤ _))
  where
  helper :
    ∀ {h} → h ≤↑ 1 + n → ¬ [ ∞ ] ⟦ unbounded ⟧ h ⊑ ⌜ n ⌝
  helper (Nat.≤↑-refl refl) =
    [ ∞ ] ⟦ unbounded ⟧ (1 + n) ⊑ ⌜ n ⌝  ↝⟨ □-head ⟩
    [ ∞ ] ⌜ 1 + n ⌝ ≤ ⌜ n ⌝              ↝⟨ ⌜⌝-mono⁻¹ ⟩
    (1 + n ≤ n)                          ↝⟨ Nat.+≮ 0 ⟩□
    ⊥                                    □
  helper {h} (Nat.≤↑-step 1+h≤1+n) =
    [ ∞ ] ⟦ unbounded ⟧ h ⊑ ⌜ n ⌝        ↝⟨ □-tail ⟩
    [ ∞ ] ⟦ unbounded ⟧ (1 + h) ⊑ ⌜ n ⌝  ↝⟨ helper 1+h≤1+n ⟩□
    ⊥                                    □

-- The maximum heap usage of unbounded is infinity.

max-unbounded-∞ : Heap-usage unbounded infinity
max-unbounded-∞ =
  no-finite-max→infinite-max unbounded λ _ → ⟦unbounded⟧⋢⌜⌝

------------------------------------------------------------------------
-- A simple optimiser

-- An optimiser that replaces subsequences of the form "alloc, alloc,
-- dealloc" with "alloc".

opt : ∀ {i} → Program ∞ → Program i
opt     []            = []
opt     (dealloc ∷ p) = dealloc ∷ λ { .force → opt (p .force) }
opt {i} (alloc   ∷ p) = opt₁ (p .force)
  module Opt where
  default : Program i
  default = alloc ∷ λ { .force → opt (p .force) }

  opt₂ : Program ∞ → Program i
  opt₂ (dealloc ∷ p″) = alloc ∷ λ { .force → opt (p″ .force) }
  opt₂ _              = default

  opt₁ : Program ∞ → Program i
  opt₁ (alloc ∷ p′) = opt₂ (p′ .force)
  opt₁ _            = default

-- The semantics of opt bounded₂ matches that of bounded.

opt-bounded₂∼bounded :
  ∀ {i n} →
  Colist.[ i ] ⟦ opt bounded₂ ⟧ n ∼ ⟦ bounded ⟧ n
opt-bounded₂∼bounded =
  refl ∷ λ { .force →
  refl ∷ λ { .force →
  opt-bounded₂∼bounded }}

-- Sometimes the optimised program's maximum heap usage is less than
-- that of the original program.

opt-improves :
  ∃ λ p → Heap-usage p ⌜ 2 ⌝ × Heap-usage (opt p) ⌜ 1 ⌝
opt-improves =
    bounded₂
  , max-bounded₂-2
  , max-respects-∼
      (Colist.symmetric-∼ opt-bounded₂∼bounded)
      (_ ∎∼)
      max-bounded-1

-- The optimised program's maximum heap usage is at most as large as
-- that of the original program (assuming that these maximums exist).

mutual

  opt-correct :
    ∀ {i m n} p →
    Heap-usage (opt p) m → Heap-usage p n → [ i ] m ≤ n
  opt-correct p max₁ max₂ =
    _⇔_.to (≲⇔least-upper-bounds-≤ max₁ max₂) (opt-correct-≲ p)

  opt-correct-≲ : ∀ {h i} p → [ i ] ⟦ opt p ⟧ h ≲ ⟦ p ⟧ h
  opt-correct-≲ {h} [] =
    ⟦ opt [] ⟧ h  ∼⟨ ∷∼∷′ ⟩≲
    h ∷′ []       ∼⟨ Colist.symmetric-∼ ∷∼∷′ ⟩□≲
    ⟦ [] ⟧ h

  opt-correct-≲ {h} (dealloc ∷ p) =
    ⟦ opt (dealloc ∷ p) ⟧ h           ∼⟨ ∷∼∷′ ⟩≲
    h ∷′ ⟦ opt (p .force) ⟧ (pred h)  ≲⟨ (cons′-≲ λ { hyp .force → opt-correct-≲ (p .force) hyp }) ⟩
    h ∷′ ⟦ p .force ⟧ (pred h)        ∼⟨ Colist.symmetric-∼ ∷∼∷′ ⟩□≲
    ⟦ dealloc ∷ p ⟧ h

  opt-correct-≲ {h} (alloc ∷ p) =
    ⟦ opt (alloc ∷ p) ⟧ h        ≡⟨⟩≲
    ⟦ Opt.opt₁ p (p .force) ⟧ h  ≲⟨ opt-correct₁ _ refl ⟩
    h ∷′ ⟦ p .force ⟧ (1 + h)    ∼⟨ Colist.symmetric-∼ ∷∼∷′ ⟩□≲
    ⟦ alloc ∷ p ⟧ h
    where
    default-correct :
      ∀ {p′ i} →
      p′ ≡ p .force →
      [ i ] ⟦ Opt.default p ⟧ h ≲ h ∷′ ⟦ p′ ⟧ (1 + h)
    default-correct refl =
      ⟦ Opt.default p ⟧ h              ∼⟨ ∷∼∷′ ⟩≲
      h ∷′ ⟦ opt (p .force) ⟧ (1 + h)  ≲⟨ (cons′-≲ λ { hyp .force → opt-correct-≲ (p .force) hyp }) ⟩□
      h ∷′ ⟦ p .force ⟧ (1 + h)

    opt-correct₁ :
      ∀ {i} p′ →
      p′ ≡ p .force →
      [ i ] ⟦ Opt.opt₁ p p′ ⟧ h ≲ h ∷′ ⟦ p′ ⟧ (1 + h)
    opt-correct₁ []             []≡ = default-correct []≡
    opt-correct₁ (dealloc ∷ p′) d∷≡ = default-correct d∷≡
    opt-correct₁ (alloc   ∷ p′) a∷≡ =
      ⟦ Opt.opt₂ p (p′ .force) ⟧ h         ≲⟨ opt-correct₂ (p′ .force) refl ⟩
      h ∷′ 1 + h ∷′ ⟦ p′ .force ⟧ (2 + h)  ∼⟨ (refl ∷ λ { .force → Colist.symmetric-∼ ∷∼∷′ }) ⟩□≲
      h ∷′ ⟦ alloc ∷ p′ ⟧ (1 + h)
      where
      default-correct′ :
        ∀ {i p″} →
        p″ ≡ p′ .force →
        [ i ] ⟦ Opt.default p ⟧ h ≲ h ∷′ 1 + h ∷′ ⟦ p″ ⟧ (2 + h)
      default-correct′ refl =
        ⟦ Opt.default p ⟧ h                  ≲⟨ default-correct refl ⟩
        h ∷′ ⟦ p .force ⟧ (1 + h)            ≡⟨ by a∷≡ ⟩≲
        h ∷′ ⟦ alloc ∷ p′ ⟧ (1 + h)          ∼⟨ (refl ∷ λ { .force → ∷∼∷′ }) ⟩□≲
        h ∷′ 1 + h ∷′ ⟦ p′ .force ⟧ (2 + h)

      opt-correct₂ :
        ∀ {i} p″ →
        p″ ≡ p′ .force →
        [ i ] ⟦ Opt.opt₂ p p″ ⟧ h ≲ h ∷′ 1 + h ∷′ ⟦ p″ ⟧ (2 + h)
      opt-correct₂ []             []≡ = default-correct′ []≡
      opt-correct₂ (alloc   ∷ p″) a∷≡ = default-correct′ a∷≡
      opt-correct₂ (dealloc ∷ p″) _   =
        ⟦ Opt.opt₂ p (dealloc ∷ p″) ⟧ h               ∼⟨ ∷∼∷′ ⟩≲
        h ∷′ ⟦ opt (p″ .force) ⟧ (1 + h)              ≲⟨ (cons′-≲ λ { hyp .force → opt-correct-≲ (p″ .force) hyp }) ⟩
        h ∷′ ⟦ p″ .force ⟧ (1 + h)                    ≲⟨ (cons′-≲ λ { hyp .force → consʳ-≲ (consʳ-≲ (_ □≲)) hyp }) ⟩
        h ∷′ 1 + h ∷′ 2 + h ∷′ ⟦ p″ .force ⟧ (1 + h)  ∼⟨ (refl ∷ λ { .force → refl ∷ λ { .force → Colist.symmetric-∼ ∷∼∷′ } }) ⟩□≲
        h ∷′ 1 + h ∷′ ⟦ dealloc ∷ p″ ⟧ (2 + h)
