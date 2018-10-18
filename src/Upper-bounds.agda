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
  ∀ {m ns o i} → ◇ i (m ≤_) ns → [ i ] ns ⊑ o → [ i ] ⌜ m ⌝ ≤ o
transitive-◇≤⊑ {m} {ns} {o} {i} = curry (
  ◇ i (m ≤_) ns × [ i ] ns ⊑ o       ↝⟨ Σ-map id swap ∘ uncurry □◇-witness ∘ swap ⟩
  (∃ λ n → m ≤ n × [ i ] ⌜ n ⌝ ≤ o)  ↝⟨ (λ { (_ , m≤n , n≤o) → transitive-≤ (⌜⌝-mono m≤n) n≤o }) ⟩□
  [ i ] ⌜ m ⌝ ≤ o                    □)

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

-- The number ⌜ n ⌝ is an upper bound of replicate m n.

replicate⊑ : ∀ {i} m {n} → [ i ] replicate m n ⊑ ⌜ n ⌝
replicate⊑ {i} zero    {n} = []
replicate⊑ {i} (suc m) {n} =                                      $⟨ (λ { _ refl → reflexive-≤ _ }) ⟩
  (∀ o → o ≡ n → [ ∞ ] ⌜ o ⌝ ≤ ⌜ n ⌝)                             ↝⟨ (λ hyp _ → hyp _ ∘ _⇔_.to ◇-replicate-suc⇔) ⟩
  (∀ o → ◇ i (o ≡_) (replicate (suc m) n) → [ ∞ ] ⌜ o ⌝ ≤ ⌜ n ⌝)  ↔⟨⟩
  (∀ o → [ i ] o ∈ replicate (suc m) n → [ ∞ ] ⌜ o ⌝ ≤ ⌜ n ⌝)     ↝⟨ _⇔_.from □⇔∈→ ⟩
  □ i (λ o → [ ∞ ] ⌜ o ⌝ ≤ ⌜ n ⌝) (replicate (suc m) n)           ↝⟨ id ⟩□
  [ i ] replicate (suc m) n ⊑ ⌜ n ⌝                               □

------------------------------------------------------------------------
-- Least upper bounds

-- The least upper bound of a colist of natural numbers.

LUB : Colist ℕ ∞ → Conat ∞ → Set
LUB ns n =
  [ ∞ ] ns ⊑ n
    ×
  (∀ n′ → [ ∞ ] ns ⊑ n′ → [ ∞ ] n ≤ n′)

-- Least upper bounds are unique.

lub-unique :
  ∀ {ns n₁ n₂ i} →
  LUB ns n₁ → LUB ns n₂ → Conat.[ i ] n₁ ∼ n₂
lub-unique (lub₁₁ , lub₁₂) (lub₂₁ , lub₂₂) =
  antisymmetric-≤ (lub₁₂ _ lub₂₁) (lub₂₂ _ lub₁₁)

-- LUB respects bisimilarity.

LUB-∼ :
  ∀ {ms ns m n} →
  Colist.[ ∞ ] ms ∼ ns → Conat.[ ∞ ] m ∼ n →
  LUB ms m → LUB ns n
LUB-∼ {ms} {ns} {m} {n} p q = Σ-map
  ([ ∞ ] ms ⊑ m  ↝⟨ □-∼ p ⟩
   [ ∞ ] ns ⊑ m  ↝⟨ □-map (flip transitive-≤ (∼→≤ q)) ⟩□
   [ ∞ ] ns ⊑ n  □)
  (λ hyp n′ →
     [ ∞ ] ns ⊑ n′  ↝⟨ □-∼ (Colist.symmetric-∼ p) ⟩
     [ ∞ ] ms ⊑ n′  ↝⟨ hyp n′ ⟩
     [ ∞ ] m ≤ n′   ↝⟨ transitive-≤ (∼→≤ (Conat.symmetric-∼ q)) ⟩□
     [ ∞ ] n ≤ n′   □)

-- The least upper bound of the empty colist is 0.

lub-[] : LUB [] ⌜ 0 ⌝
lub-[] = [] , λ _ _ → zero

-- Some lemmas that can be used to establish the least upper bound of
-- a non-empty colist.

lub-∷ˡ :
  ∀ {m ms n} →
  [ ∞ ] n ≤ ⌜ m ⌝ →
  LUB (ms .force) n →
  LUB (m ∷ ms) ⌜ m ⌝
lub-∷ˡ {m} {ms} {n} n≤m = Σ-map
  ([ ∞ ] ms .force ⊑ n      ↝⟨ (λ hyp → reflexive-≤ _ ∷ λ { .force → □-map (flip transitive-≤ n≤m) hyp }) ⟩□
   [ ∞ ] m ∷ ms    ⊑ ⌜ m ⌝  □)
  ((∀ n′ → [ ∞ ] ms .force ⊑ n′ → [ ∞ ] n     ≤ n′)  ↝⟨ (λ _ _ → □-head) ⟩□
   (∀ n′ → [ ∞ ] m ∷ ms    ⊑ n′ → [ ∞ ] ⌜ m ⌝ ≤ n′)  □)

lub-∷ʳ :
  ∀ {m ms n} →
  [ ∞ ] ⌜ m ⌝ ≤ n →
  LUB (ms .force) n →
  LUB (m ∷ ms) n
lub-∷ʳ {m} {ms} {n} m≤n = Σ-map
  ([ ∞ ] ms .force ⊑ n  ↝⟨ (λ hyp → m≤n ∷ λ { .force → hyp }) ⟩□
   [ ∞ ] m ∷ ms    ⊑ n  □)
  ((∀ n′ → [ ∞ ] ms .force ⊑ n′ → [ ∞ ] n ≤ n′)  ↝⟨ (λ hyp n′ → hyp n′ ∘ □-tail) ⟩□
   (∀ n′ → [ ∞ ] m ∷ ms    ⊑ n′ → [ ∞ ] n ≤ n′)  □)

-- If m ∷ ms has a least upper bound, then cycle m ms has the same
-- least upper bound.

lub-cycle :
  ∀ {m ms n} →
  LUB (m ∷ ms) n →
  LUB (cycle m ms) n
lub-cycle {m} {ms} {n} = Σ-map
  ([ ∞ ] m ∷ ms     ⊑ n  ↝⟨ _⇔_.from □-cycle⇔ ⟩□
   [ ∞ ] cycle m ms ⊑ n  □)
  ((∀ n′ → [ ∞ ] m ∷ ms     ⊑ n′ → [ ∞ ] n ≤ n′)  ↝⟨ (∀-cong _ λ _ → →-cong-→ (_⇔_.to □-cycle⇔) id) ⟩□
   (∀ n′ → [ ∞ ] cycle m ms ⊑ n′ → [ ∞ ] n ≤ n′)  □)

-- The least upper bound of nats is infinity.

lub-nats-infinity : LUB nats Conat.infinity
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

wlpo→lub : WLPO → (∀ ms → ∃ λ n → LUB ms n)
wlpo→lub wlpo = λ ms → lub ms , □ˢ∞→□∞ (upper-bound ms) , least ms
  where
  -- The boolean >0 ms n is true if the n-th number (counting from
  -- zero) of ms is positive.

  >0 : Colist ℕ ∞ → ℕ → Bool
  >0 []           _       = false
  >0 (m     ∷ ms) (suc n) = >0 (ms .force) n
  >0 (zero  ∷ ms) zero    = false
  >0 (suc m ∷ ms) zero    = true

  -- The number lub ms is the least upper bound of ms.

  lub : ∀ {i} → Colist ℕ ∞ → Conat i
  lub ms with wlpo (>0 ms)
  ... | inj₁ _ = zero
  ... | inj₂ _ = suc λ { .force → lub (map pred ms) }

  -- Zero is an upper bound of ms iff >0 ms is universally false.

  ⊑0⇔≡false : ∀ ms → [ ∞ ] ms ⊑ zero ⇔ (∀ n → >0 ms n ≡ false)
  ⊑0⇔≡false = λ ms → record { to = to ms; from = from ms }
    where
    to : ∀ ms → [ ∞ ] ms ⊑ zero → (∀ n → >0 ms n ≡ false)
    to _            []         _       = refl
    to (zero  ∷ ms) _          zero    = refl
    to (suc _ ∷ _)  (() ∷ _)   _
    to (m     ∷ ms) (_ ∷ ms⊑0) (suc n) = to (ms .force) (ms⊑0 .force) n

    from : ∀ {i} ms → (∀ n → >0 ms n ≡ false) → [ i ] ms ⊑ zero
    from []           _      = []
    from (suc m ∷ ms) ≡false = ⊥-elim (Bool.true≢false (≡false zero))
    from (zero  ∷ ms) ≡false =
      zero ∷ λ { .force → from (ms .force) (≡false ∘ suc) }

  -- If n .force is an upper bound of map pred ms, then suc n is an
  -- upper bound of ms. Note that the lemma is size-preserving and
  -- takes □ˢ′ to □ˢ.

  pred-lemma₁ :
    ∀ {i n} ms →
    □ˢ′ i (λ i m → [ i ] ⌜ m ⌝ ≤ n .force) (map pred ms) →
    □ˢ i (λ i m → [ i ] ⌜ m ⌝ ≤ suc n) ms
  pred-lemma₁ []       hyp = []
  pred-lemma₁ (m ∷ ms) hyp =
    helper m hyp
      ∷ λ { .force →
    pred-lemma₁ (ms .force) λ { .force → □ˢ-tail (hyp .force) }}
    where
    helper :
      ∀ {i n} m →
      □ˢ′ i (λ i m → [ i ] ⌜ m ⌝ ≤ n .force) (map pred (m ∷ ms)) →
      [ i ] ⌜ m ⌝ ≤ suc n
    helper zero    hyp = zero
    helper (suc m) hyp = suc λ { .force → □ˢ-head (hyp .force) }

  -- If suc n is an upper bound of ms, then n .force is an upper bound
  -- of map pred ms.

  pred-lemma₂ :
    ∀ {n ms i} →
    [ i ] ms ⊑ suc n →
    [ i ] map pred ms ⊑ n .force
  pred-lemma₂     []                         = []
  pred-lemma₂ {n} (_∷_ {x = m} m≤1+n ms⊑1+n) =
    (⌜ pred m ⌝        ∼⟨ ⌜⌝-pred m ⟩≤
     Conat.pred ⌜ m ⌝  ≤⟨ pred-mono m≤1+n ⟩∎
     n .force          ∎≤)
      ∷ λ { .force →
    pred-lemma₂ (ms⊑1+n .force) }

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
      least (map pred ms) (ub .force) (pred-lemma₂ ms⊑1+ub) }

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

-- Bounded m ns means that m is smaller than or equal to some element
-- in ns, or equal to zero.

Bounded : ℕ → Colist ℕ ∞ → Set
Bounded m ns = ◇ ∞ (m ≤_) ns ⊎ m ≡ zero

-- If Bounded m ns holds, then m is less than or equal to every upper
-- bound of ns.

bounded-lemma :
  ∀ {m ns n} →
  Bounded m ns → [ ∞ ] ns ⊑ n → [ ∞ ] ⌜ m ⌝ ≤ n
bounded-lemma (inj₁ ◇m≤ns) = transitive-◇≤⊑ ◇m≤ns
bounded-lemma (inj₂ refl)  = const zero

-- The empty colist is bounded by any other.

[]≲ : ∀ {ns i} → [ i ] [] ≲ ns
[]≲ = λ _ → []

-- Some derived cons-like operations.

consʳ-≲ :
  ∀ {ms ns n i} →
  [ i ] ms ≲ ns .force →
  [ i ] ms ≲ n ∷ ns
consʳ-≲ = _∘ □-tail

consˡ-≲ :
  ∀ {i m ms ns} →
  Bounded m ns →
  [ i ] ms .force ≲′ ns →
  [ i ] m ∷ ms ≲ ns
consˡ-≲ ◇m≤ns ms≲′ns ns⊑n =
  bounded-lemma ◇m≤ns ns⊑n ∷ λ { .force →
  ms≲′ns ns⊑n .force }

cons-≲ :
  ∀ {i m ms n ns} →
  Bounded m (n ∷ ns) →
  [ i ] ms .force ≲′ ns .force →
  [ i ] m ∷ ms ≲ n ∷ ns
cons-≲ {i} {m} {ms} {n} {ns} ◇m≤n∷ns =
  [ i ] ms .force ≲′ ns .force  ↝⟨ (λ { ms≲′ns hyp .force → consʳ-≲ (λ hyp → ms≲′ns hyp .force) hyp }) ⟩
  [ i ] ms .force ≲′ n ∷ ns     ↝⟨ consˡ-≲ ◇m≤n∷ns ⟩□
  [ i ] m ∷ ms ≲ n ∷ ns         □

cons′-≲ :
  ∀ {i m ms ns} →
  [ i ] ms .force ≲′ ns .force →
  [ i ] m ∷ ms ≲ m ∷ ns
cons′-≲ = cons-≲ (inj₁ (here Nat.≤-refl))

-- If the combinator consʳ-≲ had taken the primed variant of the
-- relation as an argument instead of the unprimed variant, then any
-- colist would have been bounded by any infinite colist.

consʳ-≲′→≲-infinite :
  (∀ {i ms ns n} → [ i ] ms ≲′ ns .force → [ i ] ms ≲ n ∷ ns) →
  (∀ {i ms ns} → Conat.[ ∞ ] length ns ∼ infinity → [ i ] ms ≲ ns)
consʳ-≲′→≲-infinite consʳ-≲′ {ns = []}    ()
consʳ-≲′→≲-infinite consʳ-≲′ {ns = _ ∷ _} (suc p) =
  consʳ-≲′ λ { hyp .force →
    consʳ-≲′→≲-infinite consʳ-≲′ (p .force) hyp }

-- Thus one cannot make this argument's type primed.

¬-consʳ-≲′ :
  ¬ (∀ {i ms ns n} → [ i ] ms ≲′ ns .force → [ i ] ms ≲ n ∷ ns)
¬-consʳ-≲′ =
  (∀ {i ms ns n} → [ i ] ms ≲′ ns .force → [ i ] ms ≲ n ∷ ns)       ↝⟨ consʳ-≲′→≲-infinite ⟩
  (∀ {i ms ns} → Conat.[ ∞ ] length ns ∼ infinity → [ i ] ms ≲ ns)  ↝⟨ (λ hyp → hyp (length-replicate _)) ⟩
  [ ∞ ] repeat 1 ≲ repeat 0                                         ↝⟨ _$ replicate⊑ _ ⟩
  [ ∞ ] repeat 1 ⊑ zero                                             ↝⟨ □-head ⟩
  [ ∞ ] ⌜ 1 ⌝ ≤ ⌜ 0 ⌝                                               ↝⟨ ≮0 ⟩□
  ⊥                                                                 □

-- Bisimilarity is contained in the relation.

∼→≲ : ∀ {i ms ns} → Colist.[ i ] ms ∼ ns → [ i ] ms ≲ ns
∼→≲ []          = []≲
∼→≲ (refl ∷ ps) = cons′-≲ λ { hyp .force → ∼→≲ (ps .force) hyp }

-- "Equational" reasoning combinators.

infix  -1 _□≲ finally-≲ finally-≲∼
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

finally-≲ : ∀ {i} ms ns → [ i ] ms ≲ ns → [ i ] ms ≲ ns
finally-≲ _ _ = id

syntax finally-≲ ms ns ms≲ns = ms ≲⟨ ms≲ns ⟩□ ns

finally-≲∼ : ∀ {i} ms ns → Colist.[ i ] ms ∼ ns → [ i ] ms ≲ ns
finally-≲∼ _ _ = ∼→≲

syntax finally-≲∼ ms ns ms∼ns = ms ∼⟨ ms∼ns ⟩□≲ ns

_□≲ : ∀ {i} ns → [ i ] ns ≲ ns
_□≲ {i} ns {n} =
  [ ∞ ] ns ⊑ n  ↝⟨ id ⟩□
  [ i ] ns ⊑ n  □

-- The transitivity proof can not be made size-preserving in the other
-- argument.

¬-transitivity-size-preservingʳ :
  ¬ (∀ {i ms ns os} → [ ∞ ] ms ≲ ns → [ i ] ns ≲ os → [ i ] ms ≲ os)
¬-transitivity-size-preservingʳ trans = contradiction
  where
  ones : ∀ {i} → Colist′ ℕ i
  ones .force = repeat 1

  bad : ∀ {i} → [ i ] 0 ∷ ones ≲ repeat 0
  bad {n = n} hyp = zero ∷ λ { .force {j} →  $⟨ (λ {_} → consʳ-≲ (repeat 1 □≲)) ⟩
    [ ∞ ] repeat 1 ≲ 0 ∷ ones                ↝⟨ flip trans bad ⟩
    [ j ] repeat 1 ≲ repeat 0                ↝⟨ (λ f → f hyp) ⟩□
    [ j ] repeat 1 ⊑ n                       □ }

  contradiction =              $⟨ (λ {_} → bad) ⟩
    [ ∞ ] 0 ∷ ones ≲ repeat 0  ↝⟨ _$ replicate⊑ _ ⟩
    [ ∞ ] 0 ∷ ones ⊑ zero      ↝⟨ □-head ∘ □-tail ⟩
    [ ∞ ] ⌜ 1 ⌝ ≤ ⌜ 0 ⌝        ↝⟨ ≮0 ⟩□
    ⊥                          □

-- The transitivity proof can not be made size-preserving in both
-- arguments.

¬-transitivity-size-preserving :
  ¬ (∀ {i ms ns os} → [ i ] ms ≲ ns → [ i ] ns ≲ os → [ i ] ms ≲ os)
¬-transitivity-size-preserving = ¬-transitivity-size-preservingʳ

-- If the least upper bound of ms is m and the least upper bound of ns
-- is n, then [ ∞ ] ms ≲ ns holds if and only if [ ∞ ] m ≤ n holds.

≲⇔least-upper-bounds-≤ :
  ∀ {m n ms ns} →
  LUB ms m → LUB ns n →
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

------------------------------------------------------------------------
-- Another relation that can be used to relate the least upper bounds
-- of two colists

-- [ ∞ ] ms ≂ ns means that every upper bound of ns is also an upper
-- bound of ms, and vice versa.

infix 4 [_]_≂_ [_]_≂′_

[_]_≂_ : Size → Colist ℕ ∞ → Colist ℕ ∞ → Set
[ i ] ms ≂ ns = [ i ] ms ≲ ns × [ i ] ns ≲ ms

[_]_≂′_ : Size → Colist ℕ ∞ → Colist ℕ ∞ → Set
[ i ] ms ≂′ ns = [ i ] ms ≲′ ns × [ i ] ns ≲′ ms

-- The relation is symmetric.

symmetric-≂ : ∀ {i ms ns} → [ i ] ms ≂ ns → [ i ] ns ≂ ms
symmetric-≂ = swap

-- Some derived cons-like operations.

consʳ-≂ :
  ∀ {i ms n ns} →
  Bounded n ms →
  [ i ] ms ≂ ns .force →
  [ i ] ms ≂ n ∷ ns
consʳ-≂ ◇n≤ms = Σ-map
  consʳ-≲
  (λ ns≲ms → consˡ-≲ ◇n≤ms λ hyp → λ { .force → ns≲ms hyp })

consˡ-≂ :
  ∀ {i m ms ns} →
  Bounded m ns →
  [ i ] ms .force ≂ ns →
  [ i ] m ∷ ms ≂ ns
consˡ-≂ ◇m≤ns = symmetric-≂ ∘ consʳ-≂ ◇m≤ns ∘ symmetric-≂

cons-≂ :
  ∀ {i m ms n ns} →
  Bounded m (n ∷ ns) →
  Bounded n (m ∷ ms) →
  [ i ] ms .force ≂′ ns .force →
  [ i ] m ∷ ms ≂ n ∷ ns
cons-≂ ◇m≤n∷ns ◇n≤m∷ms = Σ-map (cons-≲ ◇m≤n∷ns) (cons-≲ ◇n≤m∷ms)

cons′-≂ :
  ∀ {i m ms ns} →
  [ i ] ms .force ≂′ ns .force →
  [ i ] m ∷ ms ≂ m ∷ ns
cons′-≂ = Σ-map cons′-≲ cons′-≲

cons″-≂ :
  ∀ {i m ms ns} →
  [ i ] ms .force ≂ ns .force →
  [ i ] m ∷ ms ≂ m ∷ ns
cons″-≂ = cons′-≂ ∘ Σ-map (λ { ms≲ns hyp .force → ms≲ns hyp })
                          (λ { ns≲ms hyp .force → ns≲ms hyp })

-- Bisimilarity is contained in the relation.

∼→≂ : ∀ {i ms ns} → Colist.[ i ] ms ∼ ns → [ i ] ms ≂ ns
∼→≂ ms∼ns = ∼→≲ ms∼ns , ∼→≲ (Colist.symmetric-∼ ms∼ns)

-- "Equational" reasoning combinators.

infix  -1 _□≂ finally-≂ finally-≂∼
infixr -2 step-≂ step-≡≂ _≡⟨⟩≂_ step-∼≂ step-≂∼

step-≂ : ∀ {i} ms {ns os} →
         [ ∞ ] ns ≂ os → [ ∞ ] ms ≂ ns → [ i ] ms ≂ os
step-≂ _ = Σ-zip (step-≲ _) (flip (step-≲ _))

syntax step-≂ ms ns≂os ms≂ns = ms ≂⟨ ms≂ns ⟩ ns≂os

step-≡≂ : ∀ {i} ms {ns os} → [ i ] ns ≂ os → ms ≡ ns → [ i ] ms ≂ os
step-≡≂ _ ns≂os refl = ns≂os

syntax step-≡≂ ms ns≂os ms≡ns = ms ≡⟨ ms≡ns ⟩≂ ns≂os

_≡⟨⟩≂_ : ∀ {i} ms {ns} → [ i ] ms ≂ ns → [ i ] ms ≂ ns
_ ≡⟨⟩≂ ms≂ns = ms≂ns

step-∼≂ : ∀ {i} ms {ns os} →
          [ i ] ns ≂ os → Colist.[ ∞ ] ms ∼ ns → [ i ] ms ≂ os
step-∼≂ {i} ms {ns} {os} (ns≲os , os≲ns) ms∼ns =
    step-∼≲ ms ns≲os ms∼ns
  , λ {n} →
      [ ∞ ] ms ⊑ n  ↝⟨ □-∼ ms∼ns ⟩
      [ ∞ ] ns ⊑ n  ↝⟨ os≲ns ⟩□
      [ i ] os ⊑ n  □

syntax step-∼≂ ms ns≂os ms∼ns = ms ∼⟨ ms∼ns ⟩≂ ns≂os

step-≂∼ : ∀ {i} ms {ns os} →
          Colist.[ ∞ ] ns ∼ os → [ i ] ms ≂ ns → [ i ] ms ≂ os
step-≂∼ _ ns∼os ms≂ns =
  symmetric-≂
    (step-∼≂ _ (symmetric-≂ ms≂ns) (Colist.symmetric-∼ ns∼os))

syntax step-≂∼ ms ns∼os ms≂ns = ms ≂⟨ ms≂ns ⟩∼ ns∼os

finally-≂ : ∀ {i} ms ns → [ i ] ms ≂ ns → [ i ] ms ≂ ns
finally-≂ _ _ = id

syntax finally-≂ ms ns ms≂ns = ms ≂⟨ ms≂ns ⟩□ ns

finally-≂∼ : ∀ {i} ms ns → Colist.[ i ] ms ∼ ns → [ i ] ms ≂ ns
finally-≂∼ _ _ = ∼→≂

syntax finally-≂∼ ms ns ms∼ns = ms ∼⟨ ms∼ns ⟩□≂ ns

_□≂ : ∀ {i} ns → [ i ] ns ≂ ns
ns □≂ = (ns □≲) , (ns □≲)

-- If the least upper bound of ms is m and the least upper bound of ns
-- is n, then [ ∞ ] ms ≂ ns holds if and only if m and n are
-- bisimilar.

≂⇔least-upper-bounds-∼ :
  ∀ {m n ms ns} →
  LUB ms m → LUB ns n →
  [ ∞ ] ms ≂ ns ⇔ Conat.[ ∞ ] m ∼ n
≂⇔least-upper-bounds-∼ {⨆ms} {⨆ns} {ms} {ns} ⨆ms-lub ⨆ns-lub =
  [ ∞ ] ms ≂ ns                      ↝⟨ ≲⇔least-upper-bounds-≤ ⨆ms-lub ⨆ns-lub
                                          ×-cong
                                        ≲⇔least-upper-bounds-≤ ⨆ns-lub ⨆ms-lub ⟩
  [ ∞ ] ⨆ms ≤ ⨆ns × [ ∞ ] ⨆ns ≤ ⨆ms  ↝⟨ record { to   = uncurry antisymmetric-≤
                                               ; from = λ hyp → ∼→≤ hyp , ∼→≤ (Conat.symmetric-∼ hyp)
                                               } ⟩□
  Conat.[ ∞ ] ⨆ms ∼ ⨆ns              □

-- The predicate flip LUB n respects [ ∞ ]_≂_.

LUB-≂ : ∀ {ms ns n} → [ ∞ ] ms ≂ ns → LUB ms n → LUB ns n
LUB-≂ {ms} {ns} {n} (ms≲ns , ns≲ms) = Σ-map
  ([ ∞ ] ms ⊑ n  ↝⟨ ns≲ms ⟩□
   [ ∞ ] ns ⊑ n  □)
  ((∀ n′ → [ ∞ ] ms ⊑ n′ → [ ∞ ] n ≤ n′)  ↝⟨ (λ hyp n′ → hyp n′ ∘ ms≲ns) ⟩□
   (∀ n′ → [ ∞ ] ns ⊑ n′ → [ ∞ ] n ≤ n′)  □)

-- If [ ∞ ] ms ≂ ns holds, then ms and ns have the same least upper
-- bounds.

LUB-cong : ∀ {ms ns n} → [ ∞ ] ms ≂ ns → LUB ms n ⇔ LUB ns n
LUB-cong ms≂ns = record
  { to   = LUB-≂              ms≂ns
  ; from = LUB-≂ (symmetric-≂ ms≂ns)
  }

-- A workaround for what might be an Agda bug.

cast-≂ :
  ∀ {i} {j : Size< i} {ms ns} →
  [ i ] ms ≂ ns → [ j ] ms ≂ ns
cast-≂ p = proj₁ p , proj₂ p

------------------------------------------------------------------------
-- Variants of [_]_≲′_ and [_]_≂′_ that are intended to make certain
-- proofs easier to write

-- Using consˡ-≲/cons-≲/cons′-≲ in recursive proofs can be awkward.
-- [_]_≲″_ is intended to make it a little easier.

infix 4 [_]_≲″_

record [_]_≲″_ (i : Size) (ms ns : Colist ℕ ∞) : Set where
  coinductive
  field
    force : {j : Size< i} → [ j ] ms ≲ ns

open [_]_≲″_ public

-- Interprets [_]_≲″_.

⌊_⌋≲″ : ∀ {i ms ns} → [ i ] ms ≲″ ns → [ i ] ms ≲′ ns
⌊ p ⌋≲″ hyp .force = p .force hyp

-- [_]_≲′_ and [_]_≲″_ are pointwise logically equivalent.

≲′⇔≲″ : ∀ {i ms ns} → [ i ] ms ≲′ ns ⇔ [ i ] ms ≲″ ns
≲′⇔≲″ = record
  { to   = λ { p .force hyp → p hyp .force }
  ; from = λ { p hyp .force → p .force hyp }
  }

-- Using cons-≂/cons′-≂ in recursive proofs can be awkward. [_]_≂″_ is
-- intended to make it a little easier.

infix 4 [_]_≂″_

record [_]_≂″_ (i : Size) (ms ns : Colist ℕ ∞) : Set where
  coinductive
  field
    force : {j : Size< i} → [ j ] ms ≂ ns

open [_]_≂″_ public

-- [_]_≂′_ and [_]_≂″_ are pointwise logically equivalent.

≂′⇔≂″ : ∀ {i ms ns} → [ i ] ms ≂′ ns ⇔ [ i ] ms ≂″ ns
≂′⇔≂″ = record
  { to   = λ { p .force → (λ hyp → proj₁ p hyp .force)
                        , (λ hyp → proj₂ p hyp .force)
             }
  ; from = λ p → (λ { hyp .force → proj₁ (p .force) hyp })
               , (λ { hyp .force → proj₂ (p .force) hyp })
  }
