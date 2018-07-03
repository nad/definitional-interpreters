------------------------------------------------------------------------
-- Upper bounds of colists containing natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Upper-bounds where

open import Colist
open import Conat hiding (pred) renaming (_+_ to _⊕_; _∸_ to _⊖_)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Omniscience
open import Prelude

open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import Nat equality-with-J as Nat using (_≤_; _<_; pred)

------------------------------------------------------------------------
-- Upper bounds

-- [ ∞ ] ms ⊑ n means that n is an upper bound of every number in ms.

infix 4 [_]_⊑_ [_]_⊑′_

[_]_⊑_ : Size → Colist ℕ ∞ → Conat ∞ → Set
[ i ] ms ⊑ n = □ i (λ m → [ ∞ ] ⌜ m ⌝ ≤ n) ms

[_]_⊑′_ : Size → Colist ℕ ∞ → Conat ∞ → Set
[ i ] ms ⊑′ n = □′ i (λ m → [ ∞ ] ⌜ m ⌝ ≤ n) ms

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
  ∀ {m ns o i} → ◇ i (m ≤_) ns → [ ∞ ] ns ⊑ o → [ ∞ ] ⌜ m ⌝ ≤ o
transitive-◇≤⊑ {m} {ns} {o} {i} = curry (
  ◇ i (m ≤_) ns × [ ∞ ] ns ⊑ o       ↝⟨ Σ-map id swap ∘ uncurry □◇-witness ∘ swap ⟩
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

-- No natural number is an upper bound of nats.

nats⋢ : ∀ n → ¬ [ ∞ ] nats ⊑ ⌜ n ⌝
nats⋢ zero =
  [ ∞ ] nats ⊑ ⌜ 0 ⌝         ↝⟨ □-head ∘ □-tail ⟩
  Conat.[ ∞ ] ⌜ 1 ⌝ ≤ ⌜ 0 ⌝  ↝⟨ ≮0 ⟩□
  ⊥                          □
nats⋢ (suc n) =
  [ ∞ ] nats ⊑ ⌜ suc n ⌝          ↝⟨ □-tail ⟩
  [ ∞ ] map suc nats ⊑ ⌜ suc n ⌝  ↝⟨ □-map′ (⌜⌝-mono ∘ Nat.suc≤suc⁻¹ ∘ ⌜⌝-mono⁻¹) ⟩
  [ ∞ ] map id nats ⊑ ⌜ id n ⌝    ↝⟨ □-∼ (map-id _) ⟩
  [ ∞ ] nats ⊑ ⌜ n ⌝              ↝⟨ nats⋢ n ⟩□
  ⊥                               □

------------------------------------------------------------------------
-- Least upper bounds

-- The least upper bound of a colist of natural numbers.

Least-upper-bound : Colist ℕ ∞ → Conat ∞ → Set
Least-upper-bound ns n =
  [ ∞ ] ns ⊑ n
    ×
  (∀ n′ → [ ∞ ] ns ⊑ n′ → [ ∞ ] n ≤ n′)

-- Least upper bounds are unique.

lub-unique :
  ∀ {ns n₁ n₂ i} →
  Least-upper-bound ns n₁ → Least-upper-bound ns n₂ →
  Conat.[ i ] n₁ ∼ n₂
lub-unique (lub₁₁ , lub₁₂) (lub₂₁ , lub₂₂) =
  antisymmetric-≤ (lub₁₂ _ lub₂₁) (lub₂₂ _ lub₁₁)

-- Least-upper-bound respects bisimilarity.

Least-upper-bound-∼ :
  ∀ {ms ns m n} →
  Colist.[ ∞ ] ms ∼ ns → Conat.[ ∞ ] m ∼ n →
  Least-upper-bound ms m → Least-upper-bound ns n
Least-upper-bound-∼ {ms} {ns} {m} {n} p q = Σ-map
  ([ ∞ ] ms ⊑ m  ↝⟨ □-∼ p ⟩
   [ ∞ ] ns ⊑ m  ↝⟨ □-map (flip transitive-≤ (∼→≤ q)) ⟩□
   [ ∞ ] ns ⊑ n  □)
  (λ hyp n′ →
     [ ∞ ] ns ⊑ n′  ↝⟨ □-∼ (Colist.symmetric-∼ p) ⟩
     [ ∞ ] ms ⊑ n′  ↝⟨ hyp n′ ⟩
     [ ∞ ] m ≤ n′   ↝⟨ transitive-≤ (∼→≤ (Conat.symmetric-∼ q)) ⟩□
     [ ∞ ] n ≤ n′   □)

-- The least upper bound of the empty colist is 0.

lub-[] : Least-upper-bound [] ⌜ 0 ⌝
lub-[] = [] , λ _ _ → zero

-- Some lemmas that can be used to establish the least upper bound of
-- a non-empty colist.

lub-∷ˡ :
  ∀ {m ms n} →
  [ ∞ ] n ≤ ⌜ m ⌝ →
  Least-upper-bound (force ms) n →
  Least-upper-bound (m ∷ ms) ⌜ m ⌝
lub-∷ˡ {m} {ms} {n} n≤m = Σ-map
  ([ ∞ ] force ms ⊑ n      ↝⟨ (λ hyp → reflexive-≤ _ ∷ λ { .force → □-map (flip transitive-≤ n≤m) hyp }) ⟩□
   [ ∞ ] m ∷ ms   ⊑ ⌜ m ⌝  □)
  ((∀ n′ → [ ∞ ] force ms ⊑ n′ → [ ∞ ] n     ≤ n′)  ↝⟨ (λ _ _ → □-head) ⟩□
   (∀ n′ → [ ∞ ] m ∷ ms   ⊑ n′ → [ ∞ ] ⌜ m ⌝ ≤ n′)  □)

lub-∷ʳ :
  ∀ {m ms n} →
  [ ∞ ] ⌜ m ⌝ ≤ n →
  Least-upper-bound (force ms) n →
  Least-upper-bound (m ∷ ms) n
lub-∷ʳ {m} {ms} {n} m≤n = Σ-map
  ([ ∞ ] force ms ⊑ n  ↝⟨ (λ hyp → m≤n ∷ λ { .force → hyp }) ⟩□
   [ ∞ ] m ∷ ms   ⊑ n  □)
  ((∀ n′ → [ ∞ ] force ms ⊑ n′ → [ ∞ ] n ≤ n′)  ↝⟨ (λ hyp n′ → hyp n′ ∘ □-tail) ⟩□
   (∀ n′ → [ ∞ ] m ∷ ms   ⊑ n′ → [ ∞ ] n ≤ n′)  □)

-- If m ∷ ms has a least upper bound, then cycle m ms has the same
-- least upper bound.

lub-cycle :
  ∀ {m ms n} →
  Least-upper-bound (m ∷ ms) n →
  Least-upper-bound (cycle m ms) n
lub-cycle {m} {ms} {n} = Σ-map
  ([ ∞ ] m ∷ ms     ⊑ n  ↝⟨ _⇔_.from □-cycle⇔ ⟩□
   [ ∞ ] cycle m ms ⊑ n  □)
  ((∀ n′ → [ ∞ ] m ∷ ms     ⊑ n′ → [ ∞ ] n ≤ n′)  ↝⟨ (∀-cong _ λ _ → →-cong-→ (_⇔_.to □-cycle⇔) id) ⟩□
   (∀ n′ → [ ∞ ] cycle m ms ⊑ n′ → [ ∞ ] n ≤ n′)  □)

-- The least upper bound of nats is infinity.

lub-nats-infinity : Least-upper-bound nats Conat.infinity
lub-nats-infinity =
    (nats ⊑infinity)
  , λ n →
      [ ∞ ] nats ⊑ n                                             ↝⟨ flip no-finite→infinite ⟩
      ((∀ n → ¬ [ ∞ ] nats ⊑ ⌜ n ⌝) → Conat.[ ∞ ] n ∼ infinity)  ↝⟨ _$ nats⋢ ⟩
      Conat.[ ∞ ] n ∼ infinity                                   ↝⟨ Conat.symmetric-∼ ⟩
      Conat.[ ∞ ] infinity ∼ n                                   ↝⟨ ∼→≤ ⟩□
      [ ∞ ] infinity ≤ n                                         □

-- If WLPO holds, then the least upper bound of a colist of natural
-- numbers can be determined.
--
-- (In fact, WLPO is logically equivalent to the codomain of this
-- lemma, see Unbounded-space.wlpo⇔lub.)
--
-- I received help with this proof from Andreas Abel and Ulf Norell: I
-- had presented a proof that used LPO. Andreas Abel came up with the
-- idea for the following, less complicated proof, and Ulf Norell
-- suggested that one could get away with WLPO instead of LPO.

wlpo→lub : WLPO → (∀ ms → ∃ λ n → Least-upper-bound ms n)
wlpo→lub wlpo = λ ms → lub ms , □ˢ∞→□∞ (upper-bound ms) , least ms
  where
  -- The boolean >0 ms n is true if the n-th number (counting from
  -- zero) of ms is positive.

  >0 : Colist ℕ ∞ → ℕ → Bool
  >0 []           _       = false
  >0 (m     ∷ ms) (suc n) = >0 (force ms) n
  >0 (zero  ∷ ms) zero    = false
  >0 (suc m ∷ ms) zero    = true

  -- The number lub ms is the least upper bound of ms.

  mutual

    lub : ∀ {i} → Colist ℕ ∞ → Conat i
    lub = λ ms → case wlpo (>0 ms) of λ where
      (inj₁ _) → zero
      (inj₂ _) → suc (lub′ (map pred ms))

    lub′ : ∀ {i} → Colist ℕ ∞ → Conat′ i
    force (lub′ ms) = lub ms

  -- Zero is an upper bound of ms iff >0 ms is universally false.

  ⊑0⇔≡false : ∀ ms → [ ∞ ] ms ⊑ zero ⇔ (∀ n → >0 ms n ≡ false)
  ⊑0⇔≡false = λ ms → record { to = to ms; from = from ms }
    where
    to : ∀ ms → [ ∞ ] ms ⊑ zero → (∀ n → >0 ms n ≡ false)
    to _            []         _       = refl
    to (zero  ∷ ms) _          zero    = refl
    to (suc _ ∷ _)  (() ∷ _)   _
    to (m     ∷ ms) (_ ∷ ms⊑0) (suc n) = to (force ms) (force ms⊑0) n

    from : ∀ {i} ms → (∀ n → >0 ms n ≡ false) → [ i ] ms ⊑ zero
    from []           _      = []
    from (suc m ∷ ms) ≡false = ⊥-elim (Bool.true≢false (≡false zero))
    from (zero  ∷ ms) ≡false =
      zero ∷ λ { .force → from (force ms) (≡false ∘ suc) }

  -- If force n is an upper bound of map pred ms, then suc n is an
  -- upper bound of ms. Note that the lemma is size-preserving and
  -- takes □ˢ′ to □ˢ.

  pred-lemma₁ :
    ∀ {i n} ms →
    □ˢ′ i (λ i m → [ i ] ⌜ m ⌝ ≤ force n) (map pred ms) →
    □ˢ i (λ i m → [ i ] ⌜ m ⌝ ≤ suc n) ms
  pred-lemma₁ []       hyp = []
  pred-lemma₁ (m ∷ ms) hyp =
    helper m hyp
      ∷ λ { .force →
    pred-lemma₁ (force ms) λ { .force → □ˢ-tail (force hyp) }}
    where
    helper :
      ∀ {i n} m →
      □ˢ′ i (λ i m → [ i ] ⌜ m ⌝ ≤ force n) (map pred (m ∷ ms)) →
      [ i ] ⌜ m ⌝ ≤ suc n
    helper zero    hyp = zero
    helper (suc m) hyp = suc λ { .force → □ˢ-head (force hyp) }

  -- If suc n is an upper bound of ms, then force n is an upper bound
  -- of map pred ms.

  pred-lemma₂ :
    ∀ {n ms i} →
    [ i ] ms ⊑ suc n →
    [ i ] map pred ms ⊑ force n
  pred-lemma₂     []                         = []
  pred-lemma₂ {n} (_∷_ {x = m} m≤1+n ms⊑1+n) =
    (⌜ pred m ⌝        ∼⟨ ⌜⌝-pred m ⟩≤
     Conat.pred ⌜ m ⌝  ≤⟨ pred-mono m≤1+n ⟩∎
     force n           ∎≤)
      ∷ λ { .force →
    pred-lemma₂ (force ms⊑1+n) }

  -- The number lub ms is an upper bound of ms.

  upper-bound : ∀ {i} ms → □ˢ i (λ i m → [ i ] ⌜ m ⌝ ≤ lub ms) ms
  upper-bound {i} ms with wlpo (>0 ms)
  ... | inj₂ _ =
    pred-lemma₁ _ (λ { .force → upper-bound (map pred ms) })

  ... | inj₁ ≡false =                     $⟨ ≡false ⟩
    (∀ n → >0 ms n ≡ false)               ↝⟨ _⇔_.from (⊑0⇔≡false ms) ⟩
    [ ∞ ] ms ⊑ zero                       ↝⟨ id ⟩
    [ i ] ms ⊑ zero                       ↝⟨ _⇔_.from □ˢ⇔□ ⟩
    □ˢ i (λ _ m → [ ∞ ] ⌜ m ⌝ ≤ zero) ms  ↝⟨ id ⟩□
    □ˢ i (λ i m → [ i ] ⌜ m ⌝ ≤ zero) ms  □

  -- The number lub ms is less than or equal to every number that is
  -- an upper bound of ms.

  least :
    ∀ {i} ms ub →
    [ ∞ ] ms ⊑ ub →
    [ i ] lub ms ≤ ub
  least ms ub ms⊑ub with wlpo (>0 ms)
  least ms ub ms⊑ub | inj₁ _ = zero

  least ms (suc ub) ms⊑1+ub | inj₂ _ =
    suc λ { .force →
      least (map pred ms) (force ub) (pred-lemma₂ ms⊑1+ub) }

  least ms zero ms⊑0 | inj₂ ¬≡false =
                             $⟨ ms⊑0 ⟩
    [ ∞ ] ms ⊑ zero          ↝⟨ _⇔_.to (⊑0⇔≡false _) ⟩
    (∀ n → >0 ms n ≡ false)  ↝⟨ ¬≡false ⟩
    ⊥                        ↝⟨ ⊥-elim ⟩□
    _                        □

------------------------------------------------------------------------
-- A relation that can be used to relate the least upper bounds of two
-- colists

-- [ ∞ ] ms ≲ ns means that every upper bound of ns is also an upper
-- bound of ms.

infix 4 [_]_≲_ [_]_≲′_

[_]_≲_ : Size → Colist ℕ ∞ → Colist ℕ ∞ → Set
[ i ] ms ≲ ns = ∀ {n} → [ ∞ ] ns ⊑ n → [ i ] ms ⊑ n

[_]_≲′_ : Size → Colist ℕ ∞ → Colist ℕ ∞ → Set
[ i ] ms ≲′ ns = ∀ {n} → [ ∞ ] ns ⊑ n → [ i ] ms ⊑′ n

-- Some derived cons-like operations.

consʳ-≲ :
  ∀ {ms ns n i} →
  [ i ] ms ≲ force ns →
  [ i ] ms ≲ n ∷ ns
consʳ-≲ = _∘ □-tail

consˡ-≲ :
  ∀ {i m ms ns} →
  ◇ ∞ (m ≤_) ns →
  [ i ] force ms ≲′ ns →
  [ i ] m ∷ ms ≲ ns
consˡ-≲ ◇m≤ns ms≲′ns ns⊑n =
  transitive-◇≤⊑ ◇m≤ns ns⊑n ∷ λ { .force → force (ms≲′ns ns⊑n) }

consˡ-zero-≲ :
  ∀ {i ms ns} →
  [ i ] force ms ≲′ ns →
  [ i ] zero ∷ ms ≲ ns
consˡ-zero-≲ ms≲′ns ns⊑n =
  zero ∷ λ { .force → force (ms≲′ns ns⊑n) }

cons-≲ :
  ∀ {i m ms n ns} →
  m ≤ n →
  [ i ] force ms ≲′ force ns →
  [ i ] m ∷ ms ≲ n ∷ ns
cons-≲ {m = m} {n = n} m≤n ms≲′ns {n = n′} n∷ns⊑n′ =
  (⌜ m ⌝  ≤⟨ ⌜⌝-mono m≤n ⟩
   ⌜ n ⌝  ≤⟨ □-head n∷ns⊑n′ ⟩∎
   n′     ∎≤)
    ∷
  λ { .force → force (ms≲′ns (□-tail n∷ns⊑n′)) }

cons′-≲ :
  ∀ {i m ms ns} →
  [ i ] force ms ≲′ force ns →
  [ i ] m ∷ ms ≲ m ∷ ns
cons′-≲ = cons-≲ Nat.≤-refl

-- "Equational" reasoning combinators.

infix  -1 _□≲
infixr -2 step-≲ step-≡≲ _≡⟨⟩≲_ step-∼≲

step-≲ : ∀ {i} ms {ns os} →
         [ ∞ ] ns ≲ os → [ i ] ms ≲ ns → [ i ] ms ≲ os
step-≲ {i} ms {ns} {os} ns≲os ms≲ns {n = n} =
  [ ∞ ] os ⊑ n  ↝⟨ ns≲os ⟩
  [ ∞ ] ns ⊑ n  ↝⟨ ms≲ns ⟩□
  [ i ] ms ⊑ n  □

syntax step-≲ ms ns≲os ms≲ns = ms ≲⟨ ms≲ns ⟩ ns≲os

step-≡≲ : ∀ {i} ms {ns os} → [ i ] ns ≲ os → ms ≡ ns → [ i ] ms ≲ os
step-≡≲ _ ns≲os refl = ns≲os

syntax step-≡≲ ms ns≲os ms≡ns = ms ≡⟨ ms≡ns ⟩≲ ns≲os

_≡⟨⟩≲_ : ∀ {i} ms {ns} → [ i ] ms ≲ ns → [ i ] ms ≲ ns
_ ≡⟨⟩≲ ms≲ns = ms≲ns

step-∼≲ : ∀ {i} ms {ns os} →
          [ i ] ns ≲ os → Colist.[ i ] ms ∼ ns → [ i ] ms ≲ os
step-∼≲ {i} ms {ns} {os} ns≲os ms∼ns {n} =
  [ ∞ ] os ⊑ n  ↝⟨ ns≲os ⟩
  [ i ] ns ⊑ n  ↝⟨ □-∼ (Colist.symmetric-∼ ms∼ns) ⟩□
  [ i ] ms ⊑ n  □

syntax step-∼≲ ms ns≲os ms∼ns = ms ∼⟨ ms∼ns ⟩≲ ns≲os

_□≲ : ∀ {i} ns → [ i ] ns ≲ ns
_□≲ {i} ns {n} =
  [ ∞ ] ns ⊑ n  ↝⟨ id ⟩□
  [ i ] ns ⊑ n  □

-- If both ms ≲ ns and ns ≲ ms hold, then any least upper bound of ms
-- is also a least upper bound of ns.

Least-upper-bound-≲≳ :
  ∀ {ms ns n} →
  [ ∞ ] ms ≲ ns → [ ∞ ] ns ≲ ms →
  Least-upper-bound ms n → Least-upper-bound ns n
Least-upper-bound-≲≳ {ms} {ns} {n} ms≲ns ns≲ms = Σ-map
  ([ ∞ ] ms ⊑ n  ↝⟨ ns≲ms ⟩□
   [ ∞ ] ns ⊑ n  □)
  ((∀ n′ → [ ∞ ] ms ⊑ n′ → [ ∞ ] n ≤ n′)  ↝⟨ (λ hyp n′ → hyp n′ ∘ ms≲ns) ⟩□
   (∀ n′ → [ ∞ ] ns ⊑ n′ → [ ∞ ] n ≤ n′)  □)

-- If the least upper bound of ms is m and the least upper bound of ns
-- is n, then [ ∞ ] ms ≲ ns holds if and only if [ ∞ ] m ≤ n holds.

≲⇔least-upper-bounds-≤ :
  ∀ {m n ms ns} →
  Least-upper-bound ms m →
  Least-upper-bound ns n →
  [ ∞ ] ms ≲ ns ⇔ [ ∞ ] m ≤ n
≲⇔least-upper-bounds-≤ {⨆ms} {⨆ns} {ms} {ns} ⨆ms-lub ⨆ns-lub = record
  { to   = λ ms≲ns →          $⟨ proj₁ ⨆ns-lub ⟩
             [ ∞ ] ns ⊑ ⨆ns   ↝⟨ ms≲ns ⟩
             [ ∞ ] ms ⊑ ⨆ns   ↝⟨ proj₂ ⨆ms-lub _ ⟩□
             [ ∞ ] ⨆ms ≤ ⨆ns  □
  ; from = λ ⨆ms≤⨆ns {n} →
             [ ∞ ] ns ⊑ n   ↝⟨ proj₂ ⨆ns-lub n ⟩
             [ ∞ ] ⨆ns ≤ n  ↝⟨ transitive-≤ ⨆ms≤⨆ns ⟩
             [ ∞ ] ⨆ms ≤ n  ↝⟨ transitive-⊑≤ (proj₁ ⨆ms-lub) ⟩□
             [ ∞ ] ms ⊑ n   □
  }
