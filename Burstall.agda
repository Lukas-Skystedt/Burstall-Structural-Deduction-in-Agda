-- Imports
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat renaming (_≤_ to _≤ₙ_)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; List; [_] )
open import Data.Bool using (true; false; Bool; _∧_)
open import Function using (_∘_)
open import TotalOrder

-- The module is parametrized by the type of items (in lists and trees) and a decidable total order on it.
module Burstall (Item : Set) (Ordering : TotalOrder Item) where

private
  variable
    A B        : Set
    i i₁ i₂    : Item
    is is₁ is₂ : List Item


instance
  Item≤ : TotalOrder Item
  Item≤ = Ordering


-- Def. of concat
concat : List A → List A → List A
concat []        xs₂ = xs₂
concat (x ∷ xs₁) xs₂ = x ∷ concat xs₁ xs₂


-- Def. of lit
lit : (A → B → B) → List A → B → B
lit f []       y = y
lit f (x ∷ xs) y = f x (lit f xs y)


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

data Tree (Item : Set) : Set where
  niltree : Tree Item
  tip     : Item → Tree Item
  node    : Tree Item → Item → Tree Item → Tree Item


private
  variable
    t t₁ t₂ t₁₁ t₁₂ : Tree Item


if_then_else_ : Dec A → B → B → B
if yes A then x else y = x
if no ¬A then x else y = y


totree : Item → Tree Item → Tree Item
totree i niltree         = tip i
totree i (tip i₁)        =
  if ≤dec i₁ i
  then node (tip i₁) i (tip i)
  else node (tip i) i₁ (tip i₁)
totree i (node t₁ i₁ t₂) =
  if ≤dec i₁ i
  then node t₁ i₁ (totree i t₂)
  else node (totree i t₁) i₁ t₂


maketree : List Item → Tree Item
maketree is = lit totree is niltree


flatten : Tree Item → List (Item)
flatten niltree         = []
flatten (tip i)         = [ i ]
flatten (node t₁ i₁ t₂) = concat (flatten t₁) (flatten t₂)


sort : List (Item) → List (Item)
sort is = flatten (maketree is)


data _ᵢ≤ᵢₛ_ : Item → List Item →  Set where
  i≤[]   : i ᵢ≤ᵢₛ []
  i≤i∷is : i₁ ≤ i₂ → i₁ ᵢ≤ᵢₛ is → i₁ ᵢ≤ᵢₛ (i₂ ∷ is)


i≤is : (i : Item) → (is : List (Item)) →  Dec ( i ᵢ≤ᵢₛ is)
i≤is x [] = yes i≤[]
i≤is x₁ (x₂ ∷ xs) with ≤dec x₁ x₂ | i≤is x₁ xs
... | no proof  | _          = no λ { (i≤i∷is p _) → proof p}
... | yes _     | no ¬p      = no (λ { (i≤i∷is _ p) → ¬p p})
... | yes proof | yes proof₁ = yes (i≤i∷is proof proof₁)


data _ᵢₛ≤ᵢₛ_ : List Item → List Item →  Set where
  []≤is   : [] ᵢₛ≤ᵢₛ is
  i∷is≤is : i ᵢ≤ᵢₛ is₂ → is₁ ᵢₛ≤ᵢₛ is₂ → (i ∷ is₁) ᵢₛ≤ᵢₛ is₂


is₁≤is₂ : (is₁ is₂ : List (Item)) → Dec ( is₁ ᵢₛ≤ᵢₛ is₂)
is₁≤is₂ [] is = yes []≤is
is₁≤is₂ (i₁ ∷ is₁) is₂ with i≤is i₁ is₂ | is₁≤is₂ is₁ is₂
... | no  ¬i₁≤is₂ | _            = no λ { (i∷is≤is i₁≤is₂ _) → ¬i₁≤is₂ i₁≤is₂ }
... | yes _       | no  ¬is₁≤is₂ = no λ { (i∷is≤is _ is₁≤is₂) → ¬is₁≤is₂ is₁≤is₂}
... | yes i₁≤is₂  | yes is₁≤i₂   = yes (i∷is≤is i₁≤is₂ is₁≤i₂)


data ord : List Item → Set where
  ord[] : ord []
  ord∷  : i ᵢ≤ᵢₛ is → ord is → ord (i ∷ is)


ord? : (is : List Item) → Dec (ord is)
ord? [] = yes ord[]
ord? (i ∷ is) with i≤is i is | ord? is
... | yes p | yes p₁ = yes (ord∷ p p₁)
... | yes p | no ¬p = no (λ { (ord∷ x x₁) → ¬p x₁})
... | no ¬p | b = no (λ { (ord∷ x x₁) → ¬p x})


data _ᵢ≤ₜ_  : Item → Tree Item → Set where
  i≤niltree : i ᵢ≤ₜ niltree
  i≤tip     : i ≤ i₁ → i ᵢ≤ₜ tip i₁
  i≤node    : i ᵢ≤ₜ t₁ → i ᵢ≤ₜ t₂ → i ᵢ≤ₜ node t₁ i₁ t₂


i≤?t : (i : Item) → (t : Tree Item) → Dec (i ᵢ≤ₜ t)
i≤?t i niltree = yes i≤niltree
i≤?t i (tip i₁) with ≤dec i i₁
... | no  ¬i≤i₁ = no λ { (i≤tip i≤i₁) → ¬i≤i₁ i≤i₁}
... | yes  i≤i₁ = yes (i≤tip i≤i₁)
i≤?t i (node t₁ i₁ t₂) with i≤?t i t₁ | i≤?t i t₂
... | no  ¬i≤t₁ | _          = no λ { (i≤node i≤t₁ _) → ¬i≤t₁ i≤t₁ }
... | yes _     | no  ¬i≤t₂  = no λ { (i≤node _ i≤t₂) → ¬i≤t₂ i≤t₂ }
... | yes i≤t₁  | yes i≤t₂   = yes (i≤node i≤t₁ i≤t₂)


data _ₜ≤ᵢ_  : Tree Item → Item → Set where
  niltree≤i : niltree ₜ≤ᵢ i
  tip≤i     : i₁ ≤ i → tip i₁ ₜ≤ᵢ i
  node≤i    : t₁ ₜ≤ᵢ i → t₂ ₜ≤ᵢ i → node t₁ i₁ t₂ ₜ≤ᵢ i


t≤?i :  (t : Tree Item) → (i : Item) → Dec (t ₜ≤ᵢ i)
t≤?i niltree  i = yes niltree≤i
t≤?i (tip i₁) i with ≤dec i₁ i
... | no  ¬i₁≤i = no λ { (tip≤i i₁≤i) → ¬i₁≤i i₁≤i}
... | yes  i₁≤i = yes (tip≤i i₁≤i)
t≤?i (node t₁ i₁ t₂) i with t≤?i t₁ i | t≤?i t₂ i
... | no  ¬t₁≤i | _          = no λ { (node≤i t₁≤i _) → ¬t₁≤i t₁≤i }
... | yes _     | no  ¬t₂≤i  = no λ { (node≤i _ t₂≤i) → ¬t₂≤i t₂≤i }
... | yes t₁≤i  | yes t₂≤i   = yes  (node≤i t₁≤i t₂≤i)


data _ₜ≤ₜ_  : Tree Item → Tree Item → Set where
  niltree≤t : niltree ₜ≤ₜ t
  tip≤t     : i ᵢ≤ₜ t₂ → tip i ₜ≤ₜ t₂
  node≤t    : t₁₁ ₜ≤ₜ t₂ → t₁₂ ₜ≤ₜ t₂ →
              (node t₁₁ i t₁₂ ₜ≤ₜ t₂)


t≤?t : (t₁ t₂ : Tree Item) → Dec (t₁ ₜ≤ₜ t₂)
t≤?t niltree t = yes (niltree≤t)
t≤?t (tip i) t₂ with i≤?t i t₂
... | yes p = yes (tip≤t p)
... | no ¬p = no (λ { (tip≤t x) → ¬p x})


t≤?t (node t₁₁ i t₁₂) t₂ with t≤?t t₁₁ t₂ | t≤?t t₁₂ t₂
... | yes p | yes p₁ = yes (node≤t p p₁)
... | no ¬p | yes p = no λ { (node≤t x x₁) → ¬p x}
... | p     | no ¬p = no (λ { (node≤t x x₁) → ¬p x₁})


data ordₜ : Tree Item → Set where
  ord-nil  : ordₜ niltree
  ord-tip  : ordₜ (tip i)
  ord-node : ordₜ t₁ → ordₜ t₂ → t₁ ₜ≤ᵢ i → i ᵢ≤ₜ t₂ → ordₜ (node t₁ i t₂)


ordₜ? :  (t : Tree Item) → Dec (ordₜ t)
ordₜ? niltree = yes ord-nil
ordₜ? (tip i) = yes ord-tip
ordₜ? (node t₁ i t₂) with ordₜ? t₁ | ordₜ? t₂ | t≤?i t₁ i | i≤?t i t₂
... | no  a | b     | c     | d     = no λ { (ord-node x x₁ x₂ x₃) → a x }
... | yes a | no b  | c     | d     = no λ { (ord-node x x₁ x₂ x₃) → b x₁}
... | yes a | yes b | no  c | d     = no λ { (ord-node x x₁ x₂ x₃) → c x₂}
... | yes a | yes b | yes c | no  d = no λ { (ord-node x x₁ x₂ x₃) → d x₃}
... | yes a | yes b | yes c | yes d = yes (ord-node a b c d)


lemma : (i₁ i₂ : Item) (t : Tree Item) → i₁ ≤ i₂ → i₁ ᵢ≤ₜ t → ordₜ (totree i₂ t)
      → i₁ ᵢ≤ₜ totree i₂ t
lemma i₁ i₂ niltree  i₁≤i₂ i≤niltree       ord-tip = i≤tip i₁≤i₂
lemma i₁ i₂ (tip i₃) i₁≤i₂ (i≤tip i₁≤i₃) p
 with ≤dec i₃ i₂
... | yes _      = i≤node (i≤tip i₁≤i₃) (i≤tip i₁≤i₂)
... | no _       = i≤node (i≤tip i₁≤i₂) (i≤tip i₁≤i₃)
lemma i₁ i₂ (node t₁ i₃ t₂) i₁≤i₂ (i≤node i₁≤t₁ i₁≤t₂) _                  with ≤dec i₃ i₂
lemma i₁ i₂ (node t₁ i₃ t₂) i₁≤i₂ (i≤node i₁≤t₁ i₁≤t₂) (ord-node _ p₂ _ _) | yes _
  = i≤node i₁≤t₁ (lemma i₁ i₂ t₂ i₁≤i₂ i₁≤t₂ p₂)
lemma i₁ i₂ (node t₁ i₃ t₂) i₁≤i₂ (i≤node i₁≤t₁ i₁≤t₂) (ord-node p₁ _ _ _) | no _
  = i≤node (lemma i₁ i₂ t₁ i₁≤i₂ i₁≤t₁ p₁) i₁≤t₂


lemma2 : (t : Tree Item) (i₁ i₂ : Item) → i₂ ≤ i₁ → t ₜ≤ᵢ i₁ → ordₜ (totree i₂ t)
  → totree i₂ t ₜ≤ᵢ i₁
lemma2 niltree i₁ i₂ i₂≤i₁ _ _ = tip≤i i₂≤i₁
lemma2 (tip i₃) i₁ i₂ i₂≤i₁ (tip≤i i₃≤i₂) x₂ with ≤dec i₃ i₂
... | yes _ = node≤i (tip≤i i₃≤i₂) (tip≤i i₂≤i₁)
... | no  _ = node≤i (tip≤i i₂≤i₁) (tip≤i i₃≤i₂)
lemma2 (node t₁ i₃ t₂) i₁ i₂ i₂≤i₁ (node≤i t₁≤i₁ t₂≤i₁) x₂ with ≤dec i₃ i₂
lemma2 (node t₁ i₃ t₂) i₁ i₂ i₂≤i₁ (node≤i t₁≤i₁ t₂≤i₁) (ord-node _ p₁ _ _) | yes p
  = node≤i t₁≤i₁ (lemma2 t₂ i₁ i₂ i₂≤i₁ t₂≤i₁ p₁)
lemma2 (node t₁ i₃ t₂) i₁ i₂ i₂≤i₁ (node≤i t₁≤i₁ t₂≤i₁) (ord-node p₂ _ _ _) | no ¬p
  = node≤i (lemma2 t₁ i₁ i₂ i₂≤i₁ t₁≤i₁ p₂) t₂≤i₁


totree-ord : (i : Item) (t : Tree Item) → ordₜ t → ordₜ (totree i t)
totree-ord i niltree p = ord-tip
totree-ord i (tip i₁) ord-tip with ≤dec i₁ i
... | yes q = ord-node ord-tip ord-tip (tip≤i q)          (i≤tip ≤refl)
... | no  q = ord-node ord-tip ord-tip (tip≤i (negate q)) (i≤tip ≤refl)
totree-ord i (node t₁ i₁ t₂) (ord-node ord-t₁ ord-t₂ t₁≤i₁ i₁≤t₂) with ≤dec i₁ i
... | yes q = ord-node ord-t₁ (totree-ord i t₂ ord-t₂) t₁≤i₁ (lemma i₁ i t₂ q i₁≤t₂ (totree-ord i t₂ ord-t₂))
... | no q = ord-node (totree-ord i t₁ ord-t₁) ord-t₂ (lemma2 t₁ i₁ i (negate q) t₁≤i₁ (totree-ord i t₁ ord-t₁)) i₁≤t₂


maketree-ord : (is : List Item) → ordₜ (maketree is)
maketree-ord [] = ord-nil
maketree-ord (i ∷ is) = totree-ord i (maketree is) (maketree-ord is)


concat-ord : {is₁ is₂ : List Item} → ord is₁ → ord is₂ → is₁ ᵢₛ≤ᵢₛ is₂
         → ord (concat is₁ is₂)
concat-ord ord[] ord-is₂ is₁≤is₂ = ord-is₂
concat-ord (ord∷ i≤is₁ ord-is₁) ord-is₂ (i∷is≤is i≤is₂ is₁≤is₃)
  = ord∷ (l i≤is₁ i≤is₂) (concat-ord ord-is₁ ord-is₂ is₁≤is₃)
  where
    l : i ᵢ≤ᵢₛ is₁ → i ᵢ≤ᵢₛ is₂ → i ᵢ≤ᵢₛ concat is₁ is₂
    l i≤[] x₁ = x₁
    l (i≤i∷is x x₂) x₁ = i≤i∷is x (l x₂ x₁)


concat-i≤is : i ᵢ≤ᵢₛ is₁ → i ᵢ≤ᵢₛ is₂ → i ᵢ≤ᵢₛ concat is₁ is₂
concat-i≤is i≤[] i≤is₂                = i≤is₂
concat-i≤is (i≤i∷is i≤i₂ i≤is₁) i≤is₂ = i≤i∷is i≤i₂ (concat-i≤is i≤is₁ i≤is₂)


concat-is≤is : is₁ ᵢₛ≤ᵢₛ is → is₂ ᵢₛ≤ᵢₛ is → concat is₁ is₂ ᵢₛ≤ᵢₛ is
concat-is≤is []≤is is₂≤is                 = is₂≤is
concat-is≤is (i∷is≤is i≤is is₁≤is) is₂≤is = i∷is≤is i≤is (concat-is≤is is₁≤is is₂≤is)


flatten-i≤is : i ᵢ≤ₜ t → i ᵢ≤ᵢₛ flatten t
flatten-i≤is i≤niltree     = i≤[]
flatten-i≤is (i≤tip x)     = i≤i∷is x i≤[]
flatten-i≤is (i≤node x x₁) = concat-i≤is (flatten-i≤is x) (flatten-i≤is x₁)


flatten-is≤is : t₁ ₜ≤ₜ t₂ → flatten t₁ ᵢₛ≤ᵢₛ flatten t₂
flatten-is≤is                   niltree≤t             = []≤is
flatten-is≤is {t₂ = niltree}    (tip≤t x)             = i∷is≤is i≤[] []≤is
flatten-is≤is {t₂ = tip _}      (tip≤t (i≤tip x))     = i∷is≤is (i≤i∷is x i≤[]) []≤is
flatten-is≤is {t₂ = node _ _ _} (tip≤t (i≤node x x₁)) = i∷is≤is (concat-i≤is (flatten-i≤is x) (flatten-i≤is x₁)) []≤is
flatten-is≤is                   (node≤t x x₁)         = concat-is≤is (flatten-is≤is x) (flatten-is≤is x₁)


flatten-ord : (t : Tree Item) → ordₜ t → ord (flatten t)
flatten-ord niltree x = ord[]
flatten-ord (tip x₁) ord-tip = ord∷ i≤[] ord[]
flatten-ord (node t x₁ t₁) (ord-node x x₂ x₃ x₄) =
  concat-ord (flatten-ord t x) (flatten-ord t₁ x₂) (flatten-is≤is (l x₃ x₄))
  where
    l2 : {t₁ : Tree Item} → i₁ ≤ i₂ → i₂ ᵢ≤ₜ t₁ → i₁ ᵢ≤ₜ t₁
    l2 x i≤niltree      = i≤niltree
    l2 x (i≤tip x₁)     = i≤tip (≤trans x x₁)
    l2 x (i≤node x₁ x₂) = i≤node (l2 x x₁) (l2 x x₂)

    l :  {t₁ t₂ : Tree Item} → t₁ ₜ≤ᵢ i → i ᵢ≤ₜ t₂ → t₁ ₜ≤ₜ t₂
    l niltree≤i x₁ = niltree≤t
    l (tip≤i x) i≤niltree     = tip≤t i≤niltree
    l (tip≤i x) (i≤tip x₁)    = tip≤t (i≤tip (≤trans x x₁))
    l (tip≤i x) (i≤node y y₁) = tip≤t (i≤node (l2 x y) (l2 x y₁))
    l (node≤i x x₂) x₁        = node≤t (l x x₁) (l x₂ x₁)


sort-ord : {is : List Item} → ord (sort is)
sort-ord {is} = flatten-ord _ (maketree-ord is)
