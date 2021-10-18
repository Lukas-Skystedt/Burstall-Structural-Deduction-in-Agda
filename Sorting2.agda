-- Imports
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat renaming (_≤_ to _≤ₙ_)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false; Bool; _∧_)
open import Function using (_∘_)
open import TotalOrder

module Sorting2 where


data Type : Set₁ where
  item tree list : Set → Type

private variable
  τ τ₁ τ₂ : Type
  A B : Set

data Obj {A : Set} : Type → Set where
  item'    : A → Obj (item A)

  []       : Obj (list A)
  _∷_      : Obj {A} (item A) → Obj {A} (list A) → Obj (list A)

  niltree  : Obj (tree A)
  tip      : Obj {A} (item A) → Obj (tree A)
  node     : Obj {A} (tree A) → Obj {A} (item A) → Obj {A} (tree A) → Obj (tree A)

Item List Tree : (T : Set) → Set
Item T = Obj {T} (item T)
List T = Obj {T} (list T)
Tree T = Obj {T} (tree T)

if_then_else_ : Dec A → B → B → B
if yes A then x else y = x
if no ¬A then x else y = y

concat : List A → List A → List A
concat []        xs₂ = xs₂
concat (x ∷ xs₁) xs₂ = x ∷ concat xs₁ xs₂

lit : {τ : Set → Type} → (Item A → Obj {B} (τ B) → Obj {B} (τ B)) → List A → Obj {B} (τ B) → Obj {B} (τ B)
lit f []       y = y
lit {A} {B} {τ} f (x ∷ xs) y = f x (lit {A} {B} {τ} f xs y)

module SortStuff (A : Set) (Ordering : TotalOrder A) where

  instance
    A≤ : TotalOrder A
    A≤ = Ordering

  private
    variable
      i i₁ i₂ : Item A
      t t₁ t₂ t₁₁ t₁₂ t₂₁ t₂₂ : Tree A
      is is₁ is₂ : List A

  data _<=_ : Obj {A} τ₁ → Obj {A} τ₂ → Set where
    embed : {a a₁ : A} → a ≤ a₁ → item' a <= item' a₁

    i≤[] : i <= []
    i≤∷  : i₁ <= i₂ → i₁ <= is → i₁ <= (i₂ ∷ is)

    []≤is : [] <= is
    ∷≤is  : i <= is₂ → is₁ <= is₂ → (i ∷ is₁) <= is₂

    i≤niltree : i <= niltree
    i≤tip     : i <= i₁ → i <= tip i₁
    i≤node    : i <= t₁ → i <= t₂ → i <= node t₁ i₁ t₂

    niltree≤i : niltree <= i
    tip≤i     : i₁ <= i → tip i₁ <= i
    node≤i    : t₁ <= i → t₂ <= i → node t₁ i₁ t₂ <= i

    niltree≤t : niltree <= t
    tip≤t     : i <= t₂ → tip i <= t₂
    node≤t    : t₁₁ <= t₂ → t₁₂ <= t₂ → (node t₁₁ i t₁₂ <= t₂)

  _<=i?_ : (i₁ i₂ : Item A) → Dec (i₁ <= i₂)
  item' a₁ <=i? item' a₂ with ≤dec a₁ a₂
  ... | yes a₁≤a₂ = yes (embed a₁≤a₂)
  ... | no ¬a₁≤a₂ = no λ { (embed a₁≤a₂) → ¬a₁≤a₂ a₁≤a₂ }

  unwrap : Item A → A
  unwrap (item' a) = a

  totree : Item A → Tree A → Tree A
  totree i niltree         = tip i
  totree i (tip i₁)        =
    if i₁ <=i? i
    then node (tip i₁) i (tip i)
    else node (tip i) i₁ (tip i₁)
  totree i (node t₁ i₁ t₂) =
    if i₁ <=i? i
    then node t₁ i₁ (totree i t₂)
    else node (totree i t₁) i₁ t₂


  maketree : List A → Tree A
  maketree is = lit {τ = tree} totree is niltree


  flatten : Tree A → List A
  flatten niltree         = []
  flatten (tip i)         = i ∷ []
  flatten (node t₁ i₁ t₂) = concat (flatten t₁) (flatten t₂)


  sort : List A → List A
  sort is = flatten (maketree is)


  data ord : Obj {A} τ → Set where
    ord[] : ord []
    ord∷  : i <= is → ord is → ord (i ∷ is)

    ord-nil  : ord niltree
    ord-tip  : ord (tip i)
    ord-node : ord t₁ → ord t₂ → t₁ <= i → i <= t₂ → ord (node t₁ i t₂)


  wrap-unwrap : unwrap i₁ ≤ unwrap i₂ → i₁ <= i₂
  wrap-unwrap {i₁ = i₁} {i₂ = i₂} x with item' (unwrap i₁) | item' (unwrap i₂)
  ... | p | q = {!!}

  negate' : {a a₁ : A} → ¬ (item' a₁ <= item' a) → item' a <= item' a₁
  negate' {a = a} {a₁ = a₁} ¬i₁<=i with ≤dec a a₁
  ... | yes a≤a₁ = embed a≤a₁
  ... | no ¬a≤a₁ = let i₁<=i = embed (negate ¬a≤a₁) in ⊥-elim (¬i₁<=i i₁<=i)


  lemma : (i₁ i₂ : Item A) (t : Tree A) → i₁ <= i₂ → i₁ <= t → ord (totree i₂ t)
        → i₁ <= totree i₂ t
  lemma i₁ i₂ niltree  i₁≤i₂ i≤niltree ord-tip = i≤tip i₁≤i₂
  lemma i₁ i₂ (tip i₃) i₁≤i₂ (i≤tip i₁≤i₃) p with i₃ <=i? i₂
  ... | yes _      = i≤node (i≤tip i₁≤i₃) (i≤tip i₁≤i₂)
  ... | no _       = i≤node (i≤tip i₁≤i₂) (i≤tip i₁≤i₃)
  lemma i₁ i₂ (node t₁ i₃ t₂) i₁≤i₂ (i≤node i₁≤t₁ i₁≤t₂) _                with i₃ <=i? i₂
  lemma i₁ i₂ (node t₁ i₃ t₂) i₁≤i₂ (i≤node i₁≤t₁ i₁≤t₂) (ord-node _ p₂ _ _) | yes _
    = i≤node i₁≤t₁ (lemma i₁ i₂ t₂ i₁≤i₂ i₁≤t₂ p₂)
  lemma i₁ i₂ (node t₁ i₃ t₂) i₁≤i₂ (i≤node i₁≤t₁ i₁≤t₂) (ord-node p₁ _ _ _) | no _
    = i≤node (lemma i₁ i₂ t₁ i₁≤i₂ i₁≤t₁ p₁) i₁≤t₂

  lemma2 : (t : Tree A) (i₁ i₂ : Item A) → i₂ <= i₁ → t <= i₁ → ord (totree i₂ t)
    → totree i₂ t <= i₁
  lemma2 niltree i₁ i₂ i₂≤i₁ _ _ = tip≤i i₂≤i₁
  lemma2 (tip i₃) i₁ i₂ i₂≤i₁ (tip≤i i₃≤i₂) x₂ with i₃ <=i? i₂
  ... | yes _ = node≤i (tip≤i i₃≤i₂) (tip≤i i₂≤i₁)
  ... | no  _ = node≤i (tip≤i i₂≤i₁) (tip≤i i₃≤i₂)
  lemma2 (node t₁ i₃ t₂) i₁ i₂ i₂≤i₁ (node≤i t₁≤i₁ t₂≤i₁) x₂ with i₃ <=i? i₂
  lemma2 (node t₁ i₃ t₂) i₁ i₂ i₂≤i₁ (node≤i t₁≤i₁ t₂≤i₁) (ord-node _ p₁ _ _) | yes p
    = node≤i t₁≤i₁ (lemma2 t₂ i₁ i₂ i₂≤i₁ t₂≤i₁ p₁)
  lemma2 (node t₁ i₃ t₂) i₁ i₂ i₂≤i₁ (node≤i t₁≤i₁ t₂≤i₁) (ord-node p₂ _ _ _) | no ¬p
    = node≤i (lemma2 t₁ i₁ i₂ i₂≤i₁ t₁≤i₁ p₂) t₂≤i₁

  totree-ord : (i : Item A) (t : Tree A) → ord t → ord (totree i t)
  totree-ord i niltree ord-t = ord-tip
  totree-ord i@(item' a) (tip i₁@(item' a₁)) ord-t with i₁ <=i? i
  ... | yes i₁≤i = ord-node ord-tip ord-tip (tip≤i i₁≤i) (i≤tip (embed ≤refl))
  ... | no ¬i₁≤i = ord-node ord-tip ord-tip (tip≤i (negate' ¬i₁≤i)) (i≤tip (embed ≤refl))
  totree-ord i@(item' a) (node t₁ i₁@(item' a₁) t₂) (ord-node ord-t₁ ord-t₂ t₁≤i₁ i₁≤t₂) with i₁ <=i? i
  ... | yes i₁≤i = ord-node ord-t₁
                            (totree-ord i t₂ ord-t₂)
                            t₁≤i₁
                            (lemma i₁ i t₂ i₁≤i i₁≤t₂ (totree-ord i t₂ ord-t₂))
  ... | no ¬i₁≤i = ord-node (totree-ord i t₁ ord-t₁)
                            ord-t₂
                            (lemma2 t₁ i₁ i (negate' ¬i₁≤i) t₁≤i₁ (totree-ord i t₁ ord-t₁))
                            i₁≤t₂




  maketree-ord : (is : List A) → ord (maketree is)
  maketree-ord [] = ord-nil
  maketree-ord (is ∷ is₁) = totree-ord is (lit {τ = tree} totree is₁ niltree) (maketree-ord is₁)

  concat-ord : {is₁ is₂ : List A} → ord is₁ → ord is₂ → is₁ <= is₂ → ord (concat is₁ is₂)
  concat-ord ord[] ord-is₂ is₁≤is₂ = ord-is₂
  concat-ord (ord∷ i≤is₁ ord-is₁) ord-is₂ (∷≤is i≤is₂ is₁≤is₃)
    = ord∷ (l i≤is₁ i≤is₂) (concat-ord ord-is₁ ord-is₂ is₁≤is₃)
    where
      l : i <= is₁ → i <= is₂ → i <= concat is₁ is₂
      l i≤[] x₁ = x₁
      l (i≤∷ x x₂) x₁ = i≤∷ x (l x₂ x₁)

  trans' : {i₁ i₂ i₃ : Item A} → i₁ <= i₂ → i₂ <= i₃ → i₁ <= i₃
  trans' (embed a₁≤a₂) (embed a₂≤a₃) = embed (≤trans a₁≤a₂ a₂≤a₃)

  flatten-ord : (t : Tree A) → ord t → ord (flatten t)
  flatten-ord .niltree ord-nil = ord[]
  flatten-ord .(tip _) ord-tip = ord∷ i≤[] ord[]
  flatten-ord (node t₁ i₁ t₂) (ord-node ord-t₁ ord-t₂ t₁<=i₁ i₁<=t₂) =
    let p = flatten-ord t₁ ord-t₁
        q = flatten-ord t₂ ord-t₂
    in concat-ord p q {!!}
    where
    l : t₁ <= i₁ → i₁ <= t₂ → t₁ <= t₂
    l niltree≤i y = niltree≤t
    l (tip≤i x) i≤niltree = tip≤t i≤niltree
    l (tip≤i x) (i≤tip y) = tip≤t (i≤tip (trans' x y))
    l (tip≤i x) (i≤node y y₁) = tip≤t (i≤node {!!} {!!})
    l (node≤i x x₂) x₁ = {!!}

  -- sort-ord : {is : List A} → ord (sort is)
  -- sort-ord {is} = flatten-ord _ (maketree-ord is)
