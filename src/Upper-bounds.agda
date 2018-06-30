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
open import Function-universe equality-with-J hiding (id; _∘_)
open import Nat equality-with-J as Nat using (_≤_; _<_; pred)

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

-- [ ∞ ] ms ≲ ns implies that the least upper bound of ms is less than
-- or equal to that of ns (see ≲→least-upper-bounds-≤ below).

infix 4 [_]_≲_ [_]_≲′_

[_]_≲_ : Size → Colist ℕ ∞ → Colist ℕ ∞ → Set
[ i ] ms ≲ ns = □ i (λ m → m ≡ zero ⊎ ◇ ∞ (m ≤_) ns) ms

[_]_≲′_ : Size → Colist ℕ ∞ → Colist ℕ ∞ → Set
[ i ] ms ≲′ ns = □′ i (λ m → m ≡ zero ⊎ ◇ ∞ (m ≤_) ns) ms

-- Some derived cons-like operations.

consʳ-≲ : ∀ {ms ns n i} →
          [ i ] ms ≲ force ns →
          [ i ] ms ≲ n ∷ ns
consʳ-≲ = □-map (⊎-map id there)

cons-≲ : ∀ {i m ms n ns} →
         m ≤ n →
         [ i ] force ms ≲′ force ns →
         [ i ] m ∷ ms ≲ n ∷ ns
cons-≲ p q = inj₂ (here p) ∷ λ { .force → consʳ-≲ (force q) }

cons′-≲ : ∀ {i m ms ns} →
          [ i ] force ms ≲′ force ns →
          [ i ] m ∷ ms ≲ m ∷ ns
cons′-≲ = cons-≲ Nat.≤-refl

-- "Equational" reasoning combinators.

infix  -1 _□≲
infixr -2 step-≲ step-≡≲ _≡⟨⟩≲_ step-∼≲

step-≲ : ∀ {i} ms {ns os} →
         [ ∞ ] ns ≲ os → [ i ] ms ≲ ns → [ i ] ms ≲ os
step-≲ _ {ns} {os} ns≲os ms≲ns = □-map [ inj₁ , lemma ] ms≲ns
  where
  lemma = λ {n} →
    ◇ ∞ (n ≤_) ns                                 ↝⟨ □◇-witness ns≲os ⟩
    (∃ λ o → (o ≡ zero ⊎ ◇ ∞ (o ≤_) os) × n ≤ o)  ↝⟨ (λ { (_ , yes refl   , n≤0) → inj₁ (Nat.≤-antisymmetric n≤0 (Nat.zero≤ _))
                                                        ; (_ , inj₂ ◇o≤os , n≤o) → inj₂ (◇-map (Nat.≤-trans n≤o) ◇o≤os)
                                                        }) ⟩□
    n ≡ zero ⊎ ◇ ∞ (n ≤_) os                      □

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
n ∷ ns □≲ = cons′-≲ λ { .force → force ns □≲ }

-- If ms ≲ ns and n is an upper bound of ns, then n is also an upper
-- bound of ms.

≲⊑→⊑ :
  ∀ {i ms ns n} →
  [ i ] ms ≲ ns → [ ∞ ] ns ⊑ n → [ i ] ms ⊑ n
≲⊑→⊑ {i} {ms} {ns} {n} ms≲ns =
  [ ∞ ] ns ⊑ n                                          ↝⟨ (λ hyp {_} → flip transitive-◇≤⊑ hyp) ⟩
  (∀ {m} → ◇ ∞ (m ≤_) ns → [ ∞ ] ⌜ m ⌝ ≤ n)             ↝⟨ (λ { _   (inj₁ refl)  → zero
                                                              ; hyp (inj₂ ◇m≤ns) → hyp ◇m≤ns
                                                              }) ⟩
  (∀ {m} → m ≡ zero ⊎ ◇ ∞ (m ≤_) ns → [ ∞ ] ⌜ m ⌝ ≤ n)  ↝⟨ (λ hyp → □-map (hyp {_}) ms≲ns) ⟩□
  [ i ] ms ⊑ n                                          □

-- If both ms ≲ ns and ns ≲ ms hold, then any least upper bound of ms
-- is also a least upper bound of ns.

Least-upper-bound-≲≳ :
  ∀ {ms ns n} →
  [ ∞ ] ms ≲ ns → [ ∞ ] ns ≲ ms →
  Least-upper-bound ms n → Least-upper-bound ns n
Least-upper-bound-≲≳ {ms} {ns} {n} ms≲ns ns≲ms = Σ-map
  ([ ∞ ] ms ⊑ n  ↝⟨ ≲⊑→⊑ ns≲ms ⟩□
   [ ∞ ] ns ⊑ n  □)
  ((∀ n′ → [ ∞ ] ms ⊑ n′ → [ ∞ ] n ≤ n′)  ↝⟨ (λ hyp n′ → hyp n′ ∘ ≲⊑→⊑ ms≲ns) ⟩□
   (∀ n′ → [ ∞ ] ns ⊑ n′ → [ ∞ ] n ≤ n′)  □)

-- If [ ∞ ] ms ≲ ns, then any least upper bound of ms is less than or
-- equal to any least upper bound of ns.

≲→least-upper-bounds-≤ :
  ∀ {m n ms ns} →
  Least-upper-bound ms m →
  Least-upper-bound ns n →
  [ ∞ ] ms ≲ ns → [ ∞ ] m ≤ n
≲→least-upper-bounds-≤ {⨆ms} {⨆ns} {ms} {ns} ⨆ms-lub = flip λ ms≲ns →
  Least-upper-bound ns ⨆ns  ↝⟨ proj₁ ⟩
  [ ∞ ] ns ⊑ ⨆ns            ↝⟨ ≲⊑→⊑ ms≲ns ⟩
  [ ∞ ] ms ⊑ ⨆ns            ↝⟨ proj₂ ⨆ms-lub _ ⟩□
  [ ∞ ] ⨆ms ≤ ⨆ns           □

-- If LPO holds, the least upper bound of ms is m, and the least upper
-- bound of ns is n, then [ ∞ ] ms ≲ ns holds if and only if
-- [ ∞ ] m ≤ n holds.

lpo→≲⇔least-upper-bounds-≤ :
  LPO →
  ∀ {m n ms ns} →
  Least-upper-bound ms m →
  Least-upper-bound ns n →
  [ ∞ ] ms ≲ ns ⇔ [ ∞ ] m ≤ n
lpo→≲⇔least-upper-bounds-≤ lpo {⨆ms} {⨆ns} {ns = ns} ⨆ms-lub ⨆ns-lub =
  record
    { to   = ≲→least-upper-bounds-≤ ⨆ms-lub ⨆ns-lub
    ; from = from (proj₁ ⨆ms-lub)
    }
  where
  from : ∀ {ms i} → [ ∞ ] ms ⊑ ⨆ms → [ ∞ ] ⨆ms ≤ ⨆ns → [ i ] ms ≲ ns
  from {[]}     _        _   = []
  from {m ∷ ms} m∷ms⊑⨆ms m≤n =
    ⊎-map ≡0 (uncurry (◇≤-witness ns)) (lpo (◇≤ ns)) ∷ λ { .force →
    from (□-tail m∷ms⊑⨆ms) m≤n }
    where
    -- ◇≤ ns i is true if the value at position i in ns (if any) is
    -- greater than or equal to m.

    ◇≤ : Colist ℕ ∞ → ℕ → Bool
    ◇≤ []       _       = false
    ◇≤ (n ∷ ns) zero    = if Nat.≤⊎> m n then true else false
    ◇≤ (n ∷ ns) (suc i) = ◇≤ (force ns) i

    ◇≤-witness : ∀ ns i → ◇≤ ns i ≡ true → ◇ ∞ (m ≤_) ns
    ◇≤-witness []       _       ()
    ◇≤-witness (n ∷ ns) (suc i) ≡true = there (◇≤-witness
                                                 (force ns) i ≡true)
    ◇≤-witness (n ∷ ns) zero    ≡true with Nat.≤⊎> m n
    ◇≤-witness (n ∷ ns) zero    _     | inj₁ m≤n = here m≤n
    ◇≤-witness (n ∷ ns) zero    ()    | inj₂ _

    ⊏ : ∀ ns {i} → (∀ i → ◇≤ ns i ≡ false) → [ i ] ns ⊑ ⌜ pred m ⌝
    ⊏ []       _      = []
    ⊏ (n ∷ ns) ≡false with Nat.≤⊎> m n | ≡false 0
    ... | inj₁ _   | ()
    ... | inj₂ m>n | _  =
      ⌜⌝-mono (Nat.pred-mono m>n) ∷ λ { .force →
      ⊏ (force ns) (≡false ∘ suc) }

    ≡0 : (∀ i → ◇≤ ns i ≡ false) → m ≡ zero
    ≡0 =
      (∀ i → ◇≤ ns i ≡ false)   ↝⟨ ⊏ ns ⟩
      [ ∞ ] ns ⊑ ⌜ pred m ⌝     ↝⟨ proj₂ ⨆ns-lub ⌜ pred m ⌝ ⟩
      [ ∞ ] ⨆ns ≤ ⌜ pred m ⌝    ↝⟨ transitive-≤ m≤n ⟩
      [ ∞ ] ⨆ms ≤ ⌜ pred m ⌝    ↝⟨ transitive-≤ (□-head m∷ms⊑⨆ms) ⟩
      [ ∞ ] ⌜ m ⌝ ≤ ⌜ pred m ⌝  ↝⟨ ⌜⌝-mono⁻¹ ⟩
      (m ≤ pred m)              ↝⟨ Nat.≤pred→≡zero ⟩□
      m ≡ zero                  □
