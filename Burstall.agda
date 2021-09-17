module Burstall where

-- Imports

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_; refl; cong; sym; trans)

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat renaming (_≤_ to _≤ₙ_)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Relation.Nullary using (¬_; Dec; _because_ ; ofʸ; ofⁿ; yes; no)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; List; [_] )
open import Data.Bool using (true; false; Bool; _∧_)

-- open import Relation.Binary using (TotalOrder)
-- open import Level using (Level)

private
  variable
    A B : Set


record TotalOrder (Carrier : Set) : Set₁ where
  infix 4 _≤_
  field
    _≤_     : Carrier → Carrier → Set
    ≤trans  : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤refl   : ∀ {x}     → x ≤ x
    ≤asym   : ∀ {x y}   → x ≤ y → y ≤ x → x ≡ y
    ≤total  : ∀ {x y}   → x ≤ y ∨ y ≤ x
    ≤dec    : ∀ {x y}   → Dec (x ≤ y)


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
  ... | inj₁ m≤n         = inj₁ (s≤s m≤n)
  ... | inj₂ n≤m         = inj₂ (s≤s n≤m)

  ≤dec {{ℕ≤}} {zero}  {n}    = yes z≤n
  ≤dec {{ℕ≤}} {suc m} {zero} = no (≤ₙdecbotlemma)
    where
    ≤ₙdecbotlemma : ∀ {n} → suc n ≤ₙ zero → ⊥
    ≤ₙdecbotlemma ()

  ≤dec {{ℕ≤}} {suc m} {suc n} with ≤dec {{ℕ≤}} {m} {n}
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


-- definitions
variable
  Item : Set


data Tree (Item : Set) {{t : TotalOrder Item }} :   Set  where
  niltree : Tree Item
  tip     : Item → Tree Item
  node    : Tree Item → Item → Tree Item → Tree Item


if_then_else_ : Dec A  → B → B → B
if yes x₁ then x else y = x
if no  x₁ then x else y = y

totree : {{_ : TotalOrder Item}} → Item → Tree Item → Tree Item -- carrier Item≤ → Tree Item≤ → Tree Item≤
totree i niltree                 = tip i
totree {{potato}} i (tip i₁)        =
  if ≤dec {{potato}} {i₁} {i}
  then node (tip i₁) i (tip i)
  else node (tip i) i₁ (tip i₁)
totree {{potato}} i (node t₁ i₁ t₂) =
  if ≤dec {{potato}} {i₁} {i}
  then node t₁ i₁ (totree i t₂)
  else node (totree i t₁) i₁ t₂

maketree : {{_ : TotalOrder Item}} → List Item → Tree Item
maketree is = lit totree is niltree

flatten : {{ _ : TotalOrder Item}} → Tree Item → List (Item)
flatten niltree         = []
flatten (tip i)         = [ i ]
flatten (node t₁ i₁ t₂) = concat (flatten t₁) (flatten t₂)

--?0 ∷ ?1 != flatten (totree x₁ (lit totree is niltree)

sort : {{_ : TotalOrder Item}} → List (Item) → List (Item)
sort {{potato}} is = flatten {{potato}} (maketree {{potato}} is)

-- testsort : List (ℕ≤)
-- testsort  = sort {ℕ≤} (4 ∷ 234 ∷ 7 ∷ 2 ∷ 12 ∷ 0 ∷ [])

-- rip stonks :/


istrue : Dec A → Bool
istrue (yes x) = true
istrue (no x) = false

i<s : {{ _ : TotalOrder Item }} → List (Item) → Bool
i<s [] = true
i<s (x ∷ []) = true
i<s {{potato}} (x ∷ y ∷ xs) = istrue (≤dec {{potato}} {x} {y}) ∧ i<s {{potato}} (y ∷ xs)

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

data _ᵢ≤ᵢₛ_  {{_ : TotalOrder Item}} : Item → List Item →  Set where
  i≤[] : (i : Item) → i ᵢ≤ᵢₛ []
  i≤i∷is : (i₁ i₂ : Item) → (is : List Item) → i₁ ≤ i₂ → i₂ ᵢ≤ᵢₛ is → i₁ ᵢ≤ᵢₛ (i₂ ∷ is)

i≤is : {{ _ : TotalOrder Item}} → (i : Item) → (is : List (Item)) →  Dec ( i ᵢ≤ᵢₛ is)
i≤is x [] = yes (i≤[] x)
i≤is {{potato}}  x₁ (x₂ ∷ xs) with ≤dec {{potato}} {x₁} {x₂} | i≤is x₂ xs
... | no proof | _ = no (lemma proof)
  where
  lemma : ¬ _≤_ {{potato}} x₁ x₂ → ¬ (x₁ ᵢ≤ᵢₛ (x₂ ∷ xs))
  lemma p (i≤i∷is .x₁ .x₂ .xs x p3) = p x

... | yes proof | no proof₁ = no (lemma proof₁)
  where
  lemma : ¬ (x₂ ᵢ≤ᵢₛ xs) → ¬ (x₁ ᵢ≤ᵢₛ (x₂ ∷ xs))
  lemma x (i≤i∷is ._ ._ .xs x₁ x₂) = x x₂

... | yes proof | yes proof₁ = yes (i≤i∷is x₁ x₂ xs proof proof₁)


data _ᵢₛ₁≤ᵢₛ₂_ {{_ : TotalOrder Item}} : List Item → List Item →  Set where
  []≤is : (is : List Item) → [] ᵢₛ₁≤ᵢₛ₂ is
  i∷is₁≤is₂ : (i : Item) → (is₁ is₂ : List Item) → i ᵢ≤ᵢₛ is₂ → is₁ ᵢₛ₁≤ᵢₛ₂ is₂ → (i ∷ is₁) ᵢₛ₁≤ᵢₛ₂ is₂

is₁≤is₂ :  {{ _ : TotalOrder Item}} → (is₁ is₂  : List (Item)) → Dec ( is₁ ᵢₛ₁≤ᵢₛ₂ is₂)
is₁≤is₂ [] is = yes ([]≤is is)
is₁≤is₂ (i₁ ∷ is₁) is₂ with i≤is i₁ is₂ | is₁≤is₂ is₁ is₂
... | no proof | p = no (lemma proof)
  where lemma : ¬ (i₁ ᵢ≤ᵢₛ is₂) → ¬ (i₁ ∷ is₁) ᵢₛ₁≤ᵢₛ₂ is₂
        lemma x (i∷is₁≤is₂ .i₁ .is₁ .is₂ x₁ x₂) = x x₁

... | yes proof | no proof₁ = no (lemma proof₁)
  where lemma : ¬ (is₁ ᵢₛ₁≤ᵢₛ₂ is₂) → ¬ (i₁ ∷ is₁) ᵢₛ₁≤ᵢₛ₂ is₂
        lemma x₁ (i∷is₁≤is₂ .i₁ .is₁ ._ x p) = x₁ p

... | yes proof | yes proof₁ = yes (i∷is₁≤is₂ i₁ is₁ is₂ proof proof₁)


data ord {{_ : TotalOrder Item}} : List Item → Set where
  ord[] : ord []
  ord∷  : (i : Item) → (is : List Item) → i ᵢ≤ᵢₛ is → ord (i ∷ is)

ord? : {{ _ : TotalOrder Item}} → (is : List Item) → Dec (ord is)
ord? [] = yes ord[]
ord? (i ∷ is) with i≤is i is
... | no proof = no (lemma proof) 
  where
    lemma : ¬ (i ᵢ≤ᵢₛ is) → ¬ ord (i ∷ is)
    lemma x (ord∷ .i .is x₁) = x x₁
... | yes proof = yes (ord∷ i is proof)


-- ord?sort : {{ _ : TotalOrder Item}} → ∀ {is : List Item}  → ord (sort is)
-- ord?sort {Item} ⦃ x ⦄ {[]} = ord[]
-- ord?sort {Item} ⦃ x ⦄ {x₁ ∷ is} with (sort (x₁ ∷ is))
-- ... | a = {!!}

data _ᵢ≤ₜ_ {{_ : TotalOrder Item}} : Item → Tree Item → Set where
  i≤niltree : (i : Item) → i ᵢ≤ₜ niltree
  i≤tip     : (i i₁ : Item) → i ≤ i₁ → i ᵢ≤ₜ tip i₁
  i≤node    : (i i₁ : Item) → (t₁ t₂ : Tree Item) → i ᵢ≤ₜ t₁ → i ᵢ≤ₜ t₂ → i ᵢ≤ₜ node t₁ i₁ t₂

i≤?t : {{_ : TotalOrder Item}} → (i : Item) → (t : Tree Item) → Dec (i ᵢ≤ₜ t)
i≤?t i niltree = yes (i≤niltree i)
i≤?t {{potato}} i (tip i₁) with ≤dec {{potato}} {i} {i₁}
... | no proof = no (lemma proof)
  where
    lemma : ¬ (_≤_ {{potato}} i) i₁ → ¬ (i ᵢ≤ₜ tip i₁)
    lemma x (i≤tip .i .i₁ x₁) = x x₁
... | yes proof = yes (i≤tip i i₁ proof)

i≤?t i (node t₁ i₁ t₂) with i≤?t i t₁ | i≤?t i t₂
... | no proof | p2 = no (lemma proof)
    where
    lemma : ¬ (i ᵢ≤ₜ t₁) → ¬ (i ᵢ≤ₜ node t₁ i₁ t₂)
    lemma x (i≤node .i .i₁ .t₁ .t₂ x₁ x₂) = x x₁
... | yes proof | no proof₁ = no (lemma proof₁)
    where
    lemma : ¬ (i ᵢ≤ₜ t₂) → ¬ (i ᵢ≤ₜ node t₁ i₁ t₂)
    lemma x (i≤node .i .i₁ .t₁ .t₂ x₁ x₂) = x x₂
... | yes proof | yes proof₁ = yes (i≤node i i₁ t₁ t₂ proof proof₁)

-- (istrue (≤dec {{potato}} {x₁} {x})) && (i≤is {{potato}} xs x)
-- mutual

--   data OrdList (A : Set) : Set where
--     []ₒ  : OrdList A
--     _∷ₒ_ : {x : A} → {xs : OrdList A} → x c xs → OrdList A

--   -- bevis här
-- bygger listor → bevisar att ordningen håller → gör till ordlist

-- elem<list : 

-- !SKÄMS!
