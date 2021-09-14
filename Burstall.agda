module Burstall where

-- Imports

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_; refl; cong; sym; trans)

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat renaming (_≤_ to _≤ₙ_)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; List; [_] )
open import Data.Bool using (true; false; Bool; _∧_)

-- open import Relation.Binary using (TotalOrder)
-- open import Level using (Level)

private
  variable
    A B : Set

-- TODO: Maybe replace with Dec from Relation.Nullary?
data Decidable : Set → Set where
  yes : A → Decidable A
  no  : ¬ A → Decidable A


record TotalOrder : Set₁ where
  infix 4 _≤_
  field
    Carrier : Set
    _≤_     : Carrier → Carrier → Set
    ≤trans  : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤refl   : ∀ {x}     → x ≤ x
    ≤asym   : ∀ {x y}   → x ≤ y → y ≤ x → x ≡ y
    ≤total  : ∀ {x y}   → x ≤ y ∨ y ≤ x
    ≤dec    : ∀ {x y}   → Decidable (x ≤ y)


ℕ≤ : TotalOrder
ℕ≤ = record
       { Carrier = ℕ
       ; _≤_     = _≤ₙ_
       ; ≤trans  = ≤ₙtrans
       ; ≤refl   = ≤ₙrefl
       ; ≤asym   = ≤ₙasym
       ; ≤total  = ≤ₙtotal
       ; ≤dec    = ≤ₙdec
       }
   where
   ≤ₙtrans : ∀ {m n z} → m ≤ₙ n → n ≤ₙ z → m ≤ₙ z
   ≤ₙtrans z≤n     _       = z≤n
   ≤ₙtrans (s≤s a) (s≤s b) = s≤s (≤ₙtrans a b)

   ≤ₙrefl : ∀ {m} → m ≤ₙ m
   ≤ₙrefl {zero}  = z≤n
   ≤ₙrefl {suc _} = s≤s ≤ₙrefl

   ≤ₙasym : ∀ {m n} → m ≤ₙ n → n ≤ₙ m → m ≡ n
   ≤ₙasym z≤n       z≤n       = refl
   ≤ₙasym (s≤s m≤n) (s≤s n≤m) = cong suc (≤ₙasym m≤n n≤m)

   ≤ₙtotal  : ∀ {m n} → m ≤ₙ n ∨ n ≤ₙ m
   ≤ₙtotal {zero}  {_}    = inj₁ z≤n
   ≤ₙtotal {suc _} {zero} = inj₂ z≤n
   ≤ₙtotal {suc m} {suc n} with ≤ₙtotal {m} {n}
   ... | inj₁ m≤n         = inj₁ (s≤s m≤n)
   ... | inj₂ n≤m         = inj₂ (s≤s n≤m)

   ≤ₙdecbotlemma : ∀ {n} → suc n ≤ₙ zero → ⊥
   ≤ₙdecbotlemma ()


   ≤ₙdec : ∀ {m n} → Decidable (m ≤ₙ n)
   ≤ₙdec {zero}  {n}    = yes z≤n
   ≤ₙdec {suc m} {zero} = no ≤ₙdecbotlemma
   ≤ₙdec {suc m} {suc n} with ≤ₙdec {m} {n}
   ... | yes m≤n        = yes (s≤s m≤n)
   ... | no ¬m≤n        = no λ sm≤sn → ¬m≤n (≤ₙ-dec sm≤sn)
     where
      ≤ₙ-dec : ∀ {m n} → suc m ≤ₙ suc n → m ≤ₙ n
      ≤ₙ-dec (s≤s m≤n) = m≤n


-- Def. of concat
concat : List A → List A → List A
concat []        xs₂ = xs₂
concat (x ∷ xs₁) xs₂ = x ∷ concat xs₁ xs₂

-- ^ test
ctest : _
ctest = concat (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ [])


-- Def. of lit
lit : (A → B → B) → List A → B → B
lit f []       y = y
lit f (x ∷ xs) y = f x (lit f xs y)

-- ^ test
ltest : _
ltest = lit _+_ (2 ∷ 3 ∷ 4 ∷ []) 1

lit-concat-lemma : (f : (A → B → B)) (xs1 xs2 : List A) (y : B)
                 → lit f (concat xs1 xs2) y ≡ lit f xs1 (lit f xs2 y)
lit-concat-lemma f (x ∷ xs1) xs2 y =
  begin
  lit f (concat (x ∷ xs1) xs2) y
  ≡⟨⟩ -- by def. of concat
  lit f (x ∷ concat xs1 xs2) y
  ≡⟨⟩ -- by def of lit
  f x (lit f (concat xs1 xs2) y)
  ≡⟨ cong (f x) (lit-concat-lemma f xs1 xs2 y) ⟩ -- by IH
  f x (lit f xs1 (lit f xs2 y))
  ≡⟨⟩ -- by def. of lit
  lit f (x ∷ xs1) (lit f xs2 y) ∎
lit-concat-lemma f [] xs2 y =
  begin
  lit f (concat [] xs2) y
  ≡⟨⟩ -- By def. of concat
  lit f xs2 y
  ≡⟨⟩
  lit f [] (lit f xs2 y) ∎


p-lemma : {xs : List A} → {y₀ : A} → {f : A → A → A} → {P : A → Set} →
         P y₀ →
         (∀ {x y} → P y → P (f x y)) →
         P (lit f xs y₀)
p-lemma {xs = []}     {y₀} {f} {P} Pyₒ impl = Pyₒ
p-lemma {xs = x ∷ xs} {y₀} {f} {P} Pyₒ impl =
  let IH = p-lemma {xs = xs} {y₀} {f} {P} Pyₒ impl
  in impl IH

carrier : (Item : TotalOrder) → Set
carrier = TotalOrder.Carrier


-- definitions
variable
  Item≤ : TotalOrder


data Tree : (t : TotalOrder) →  Set  where
  niltree : Tree Item≤
  tip     : carrier Item≤ → Tree Item≤
  node    : Tree Item≤ → carrier Item≤ → Tree Item≤ → Tree Item≤


if_then_else_ : Decidable A  → B → B → B
if yes x₁ then x else y = x
if no  x₁ then x else y = y

totree : carrier Item≤ → Tree Item≤ → Tree Item≤
totree i niltree                 = tip i
totree {Item≤} i (tip i₁)        =
  if TotalOrder.≤dec Item≤ {i₁} {i}
  then node (tip i₁) i (tip i)
  else node (tip i) i₁ (tip i₁)
totree {Item≤} i (node t₁ i₁ t₂) =
  if TotalOrder.≤dec Item≤ {i₁} {i}
  then node t₁ i₁ (totree i t₂)
  else node (totree i t₁) i₁ t₂

maketree : List (carrier Item≤) → Tree Item≤
maketree is = lit totree is niltree

flatten : Tree Item≤ → List (carrier Item≤)
flatten niltree         = []
flatten (tip i)         = [ i ]
flatten (node t₁ i₁ t₂) = concat (flatten t₁) (flatten t₂)

sort : List (carrier Item≤) → List (carrier Item≤)
sort {Item≤} is = flatten {Item≤} (maketree {Item≤} is)

testsort : List (carrier ℕ≤)
testsort  = sort {ℕ≤} (4 ∷ 234 ∷ 7 ∷ 2 ∷ 12 ∷ 0 ∷ [])


stonks : {tot : TotalOrder} → (carrier tot → List (carrier tot) → Set)
stonks = {!!}

istrue : Decidable A → Bool
istrue (yes x) = true
istrue (no x) = false

i<s : List (carrier Item≤) → Bool
i<s [] = true
i<s (x ∷ []) = true
i<s {Item≤} (x ∷ y ∷ xs) = istrue (TotalOrder.≤dec Item≤ {x} {y}) ∧ i<s {Item≤} (y ∷ xs)

-- mutual

--   data OrdList (A : Set) : Set where
--     []ₒ  : OrdList A
--     _∷ₒ_ : {x : A} → {xs : OrdList A} → x c xs → OrdList A

--   -- bevis här
-- bygger listor → bevisar att ordningen håller → gör till ordlist

-- elem<list : 

-- !SKÄMS!
