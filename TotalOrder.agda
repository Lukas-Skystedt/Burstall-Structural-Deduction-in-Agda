module TotalOrder where

import Relation.Binary.PropositionalEquality as Eq

open        Eq               using    (_≡_; refl; cong)
open import Data.Nat         using    (ℕ)
                             renaming (_≤_ to _≤ₙ_)
open import Data.Empty       using    (⊥; ⊥-elim)
open import Relation.Nullary using    (¬_; Dec; yes; no)
open import Data.Sum         renaming (_⊎_ to _∨_)


record TotalOrder (Carrier : Set) : Set₁ where
  infix 4 _≤_
  field
    _≤_     : Carrier → Carrier → Set
    ≤trans  : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤refl   : ∀ {x}     → x ≤ x
    ≤asym   : ∀ {x y}   → x ≤ y → y ≤ x → x ≡ y
    ≤total  : ∀ {x y}   → x ≤ y ∨ y ≤ x
    ≤dec    : ∀ x → ∀ y → Dec (x ≤ y)

  negate : ∀ {x y} → ¬ x ≤ y → y ≤ x
  negate {x} {y} ¬x≤y with ≤total {x} {y}
  ... | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
  ... | inj₂ y≤x = y≤x


open TotalOrder {{...}} public
instance
  ℕ≤ : TotalOrder ℕ
  _≤_   {{ℕ≤}}  = _≤ₙ_

  ≤trans {{ℕ≤}} z≤n     _       = z≤n
  ≤trans {{ℕ≤}} (s≤s a) (s≤s b) = s≤s (≤trans a b)

  ≤refl {{ℕ≤}} {zero}  = z≤n
  ≤refl {{ℕ≤}} {suc _} = s≤s ≤refl

  ≤asym {{ℕ≤}} z≤n       z≤n       = refl
  ≤asym {{ℕ≤}} (s≤s m≤n) (s≤s n≤m) = cong suc (≤asym m≤n n≤m)

  ≤total {{ℕ≤}} {zero}  {_}    = inj₁ z≤n
  ≤total {{ℕ≤}} {suc _} {zero} = inj₂ z≤n
  ≤total {{ℕ≤}} {suc m} {suc n} with ≤total {{ℕ≤}} {m} {n}
  ... | inj₁ m≤n               = inj₁ (s≤s m≤n)
  ... | inj₂ n≤m               = inj₂ (s≤s n≤m)

  ≤dec {{ℕ≤}} zero    n    = yes z≤n
  ≤dec {{ℕ≤}} (suc m) zero = no (λ ())
  ≤dec {{ℕ≤}} (suc m) (suc n) with ≤dec {{ℕ≤}} m n
  ... | yes m≤n            = yes (s≤s m≤n)
  ... | no ¬m≤n            = no λ { (s≤s m≤n) → ¬m≤n m≤n}
