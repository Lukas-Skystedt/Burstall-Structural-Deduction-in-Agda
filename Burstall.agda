module Burstall where

-- Imports
open import Agda.Builtin.Bool

open import Agda.Builtin.List


import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_; refl; cong; sym; trans)

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat renaming (_≤_ to _leq_)
open import Data.Sum renaming (_⊎_ to _∨_)

-- open import Relation.Binary using (TotalOrder)


private
  variable
    A B : Set

record TotalOrder : Set₁ where
  infix 4 _≤_
  field
    Carrier : Set
    _≤_     : Carrier → Carrier → Set
    ≤trans  : {x y z : Carrier} → x ≤ y → y ≤ z → x ≤ z
    ≤ref    : {x : Carrier}     → x ≤ x
    ≤asym   : {x y : Carrier}   → x ≤ y → y ≤ x → x ≡ y
    ≤total  : {x y : Carrier}   → x ≤ y ∨ y ≤ x


ℕ≤ : TotalOrder
ℕ≤ = record
       { Carrier = ℕ
       ; _≤_     = _leq_
       ; ≤trans  = leqtrans
       ; ≤ref    = leqrefl
       ; ≤asym   = leqasym
       ; ≤total  = leqtotal
       }
   where
   leqtrans  : ∀ {x y z } → x leq y → y leq z → x leq z
   leqtrans z≤n y = z≤n
   leqtrans (s≤s y) (s≤s z) = s≤s (leqtrans y z)

   leqrefl : ∀ {x} → x leq x
   leqrefl {zero} = z≤n
   leqrefl {suc x} = s≤s leqrefl

   leqasym   : ∀ {x y}   → x leq y → y leq x → x ≡ y
   leqasym z≤n z≤n = refl
   leqasym (s≤s x) (s≤s y) = cong suc (leqasym x y)

   leqtotal  : ∀ {x y }   → x leq y ∨ y leq x
   leqtotal {zero} {n} = inj₁ z≤n
   leqtotal {n} {zero} = inj₂ z≤n
   leqtotal {suc x} {suc y} with leqtotal {x} {y}
   ... | inj₁ x₁ = inj₁ (s≤s x₁)
   ... | inj₂ y₁ = inj₂ (s≤s y₁)

-- Def. of concat
concat : List A → List A → List A
concat [] l2       = l2
concat (x ∷ l1) l2 = x ∷ concat l1 l2

-- ^ test
ctest : _
ctest = concat (1 ∷ (2 ∷ (3 ∷ []))) (4 ∷ [])


-- Def. of lit
lit : (A → B → B) → List A → B → B
lit f [] y = y
lit f (x ∷ xs) y = f x (lit f xs y)

-- ^ test
ltest : _
ltest = lit _+_ (2 ∷ 3 ∷ 4 ∷ []) 1

lit-concat-lemma : (f : (A → B → B)) (xs1 xs2 : List A) (y : B)
                 → lit f (concat xs1 xs2) y ≡ lit f xs1 (lit f xs2 y)
lit-concat-lemma f (x ∷ xs1) xs2 y =
  begin
  lit f (concat (x ∷ xs1) xs2) y
  ≡⟨⟩ -- by def of concat
  lit f (x ∷ concat xs1 xs2) y
  ≡⟨⟩  -- by def of lit
  f x (lit f (concat xs1 xs2) y)
  ≡⟨ cong (f x) (lit-concat-lemma f xs1 xs2 y) ⟩  -- by IH
  f x (lit f xs1 (lit f xs2 y))
  ≡⟨⟩ -- by def. of lit
  lit f (x ∷ xs1) (lit f xs2 y) ∎
lit-concat-lemma f [] xs2 y =
  begin
  lit f (concat [] xs2) y -- LHS
  ≡⟨⟩
  lit f xs2 y             -- By def. of concat
  ≡⟨⟩
  lit f [] (lit f xs2 y) ∎


p-lemma : {xs : List A} → {y₀ : A} → {f : A → A → A} → {P : A → Set} →
         P y₀ →
         (∀ {x y} → P y → P (f x y)) →
         P (lit f xs y₀)
p-lemma {xs = []} {y₀} {f} {P} Pyₒ impl = Pyₒ
p-lemma {xs = x ∷ xs} {y₀} {f} {P} Pyₒ impl =
  let IH = p-lemma {xs = xs} {y₀} {f} {P} Pyₒ impl
  in impl IH

carrier : (Item : TotalOrder) → Set
carrier x = TotalOrder.Carrier x

-- definitions
variable
  Item≤ : TotalOrder
  Item : carrier Item≤


data Tree (Item : TotalOrder) : Set  where
  node    : Tree Item → carrier Item → Tree Item → Tree Item
  tip     : carrier Item → Tree Item
  niltree : Tree Item
