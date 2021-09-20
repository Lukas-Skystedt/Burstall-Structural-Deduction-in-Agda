module Burstall where

-- Imports

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; Dec; _because_ ; ofʸ; ofⁿ; yes; no)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat renaming (_≤_ to _≤ₙ_)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; List; [_] )
open import Data.Bool using (true; false; Bool; _∧_)
open import Function using (_∘_)

-- open import Relation.Binary using (TotalOrder)
-- open import Level using (Level)

private
  variable
    A B : Set

-- TODO:
-- Clean up whitespace
-- Figure out if ⦃ potato ⦄ can be omitted in more cases
-- Replace many lemmas with patterm matching lambdas. Rename proof variables.
-- Consistent naming of relations and their decision procedures


record TotalOrder (Carrier : Set) : Set₁ where
  infix 4 _≤_
  field
    _≤_     : Carrier → Carrier → Set
    ≤trans  : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤refl   : ∀ {x}     → x ≤ x
    ≤asym   : ∀ {x y}   → x ≤ y → y ≤ x → x ≡ y
    ≤total  : ∀ {x y}   → x ≤ y ∨ y ≤ x
    ≤dec    : ∀ x → ∀ y → Dec (x ≤ y)


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

lit-concat-lemma : (f : (A → B → B)) (xs₁ xs₂ : List A) (y : B)
                 → lit f (concat xs₁ xs₂) y ≡ lit f xs₁ (lit f xs₂ y)
lit-concat-lemma f (x ∷ xs₁) xs₂ y =
  begin
  lit f (concat (x ∷ xs₁) xs₂) y
  ≡⟨⟩ -- by def. of concat
  lit f (x ∷ concat xs₁ xs₂) y
  ≡⟨⟩ -- by def of lit
  f x (lit f (concat xs₁ xs₂) y)
  ≡⟨ cong (f x) (lit-concat-lemma f xs₁ xs₂ y) ⟩ -- by IH
  f x (lit f xs₁ (lit f xs₂ y))
  ≡⟨⟩ -- by def. of lit
  lit f (x ∷ xs₁) (lit f xs₂ y) ∎
lit-concat-lemma f [] xs₂ y =
  begin
  lit f (concat [] xs₂) y
  ≡⟨⟩ -- By def. of concat
  lit f xs₂ y
  ≡⟨⟩
  lit f [] (lit f xs₂ y) ∎


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

data Tree (Item : Set) {{t : TotalOrder Item }} : Set where
  niltree : Tree Item
  tip     : Item → Tree Item
  node    : Tree Item → Item → Tree Item → Tree Item

if_then_else_ : Dec A → B → B → B
if yes A then x else y = x
if no ¬A then x else y = y

totree : {{_ : TotalOrder Item}} → Item → Tree Item → Tree Item
totree i niltree         = tip i
totree i (tip i₁)        =
  if ≤dec i₁ i
  then node (tip i₁) i (tip i)
  else node (tip i) i₁ (tip i₁)
totree i (node t₁ i₁ t₂) =
  if ≤dec i₁ i
  then node t₁ i₁ (totree i t₂)
  else node (totree i t₁) i₁ t₂


maketree : {{_ : TotalOrder Item}} → List Item → Tree Item
maketree is = lit totree is niltree


flatten : {{ _ : TotalOrder Item}} → Tree Item → List (Item)
flatten niltree         = []
flatten (tip i)         = [ i ]
flatten (node t₁ i₁ t₂) = concat (flatten t₁) (flatten t₂)


sort : {{_ : TotalOrder Item}} → List (Item) → List (Item)
sort is = flatten (maketree is)


data _ᵢ≤ᵢₛ_  {{_ : TotalOrder Item}} : Item → List Item →  Set where
  i≤[] : (i : Item) → i ᵢ≤ᵢₛ []
  i≤i∷is : (i₁ i₂ : Item) → (is : List Item) → i₁ ≤ i₂ → i₂ ᵢ≤ᵢₛ is → i₁ ᵢ≤ᵢₛ (i₂ ∷ is)

i≤is : {{ _ : TotalOrder Item}} → (i : Item) → (is : List (Item)) →  Dec ( i ᵢ≤ᵢₛ is)
i≤is x [] = yes (i≤[] x)
i≤is x₁ (x₂ ∷ xs) with ≤dec x₁ x₂ | i≤is x₂ xs
... | no proof  | _          = no λ { (i≤i∷is _ _ _ x _) → proof x}
... | yes _     | no ¬p      = no λ { (i≤i∷is _ _ _ _ p) → ¬p p }
... | yes proof | yes proof₁ = yes (i≤i∷is x₁ x₂ xs proof proof₁)


data _ᵢₛ₁≤ᵢₛ₂_ {{_ : TotalOrder Item}} : List Item → List Item →  Set where
  []≤is : (is : List Item) → [] ᵢₛ₁≤ᵢₛ₂ is
  i∷is₁≤is₂ : (i : Item) → (is₁ is₂ : List Item) → i ᵢ≤ᵢₛ is₂ → is₁ ᵢₛ₁≤ᵢₛ₂ is₂ → (i ∷ is₁) ᵢₛ₁≤ᵢₛ₂ is₂

is₁≤is₂ :  {{ _ : TotalOrder Item}} → (is₁ is₂  : List (Item)) → Dec ( is₁ ᵢₛ₁≤ᵢₛ₂ is₂)
is₁≤is₂ [] is = yes ([]≤is is)
is₁≤is₂ (i₁ ∷ is₁) is₂ with i≤is i₁ is₂ | is₁≤is₂ is₁ is₂
... | no  ¬i₁≤is₂ | _            = no λ { (i∷is₁≤is₂ _ _ _ i₁≤is₂ _) → ¬i₁≤is₂ i₁≤is₂ }
... | yes _       | no  ¬is₁≤is₂ = no λ { (i∷is₁≤is₂ _ _ _ _ is₁≤is₂) → ¬is₁≤is₂ is₁≤is₂}
... | yes i₁≤is₂  | yes is₁≤i₂   = yes (i∷is₁≤is₂ i₁ is₁ is₂ i₁≤is₂ is₁≤i₂)


data ord {{_ : TotalOrder Item}} : List Item → Set where
  ord[] : ord []
  ord∷  : (i : Item) → (is : List Item) → i ᵢ≤ᵢₛ is → ord (i ∷ is)

ord? : {{ _ : TotalOrder Item}} → (is : List Item) → Dec (ord is)
ord? [] = yes ord[]
ord? (i ∷ is) with i≤is i is
... | no  ¬i≤is = no λ { (ord∷ .i .is i≤is) → ¬i≤is i≤is}
... | yes  i≤is = yes (ord∷ i is i≤is)


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
i≤?t i (tip i₁) with ≤dec i i₁
... | no  ¬i≤i₁ = no λ { (i≤tip .i .i₁ i≤i₁) → ¬i≤i₁ i≤i₁}
... | yes  i≤i₁ = yes (i≤tip i i₁ i≤i₁)
i≤?t i (node t₁ i₁ t₂) with i≤?t i t₁ | i≤?t i t₂
... | no  ¬i≤t₁ | _          = no λ { (i≤node .i .i₁ .t₁ .t₂ i≤t₁ _) → ¬i≤t₁ i≤t₁ }
... | yes _     | no  ¬i≤t₂  = no λ { (i≤node .i .i₁ .t₁ .t₂ _ i≤t₂) → ¬i≤t₂ i≤t₂ }
... | yes i≤t₁  | yes i≤t₂   = yes (i≤node i i₁ t₁ t₂ i≤t₁ i≤t₂)

-- mutual

--   data OrdList (A : Set) : Set where
--     []ₒ  : OrdList A
--     _∷ₒ_ : {x : A} → {xs : OrdList A} → x c xs → OrdList A

