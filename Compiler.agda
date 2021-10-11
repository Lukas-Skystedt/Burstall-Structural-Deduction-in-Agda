import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat renaming (_≤_ to _≤ₙ_)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_; List; [_] ) renaming ([] to nil)
open import Data.Bool using (true; false; Bool; _∧_)
open import Function using (_∘_)

module Compiler where

private
  variable A B C : Set

-- Abstract syntax of source language
data Atom : Set where
  atom : ℕ → Atom

data Operator : Set where
  operator : Atom → Operator

data Identifier : Set where
  ident : Atom → Identifier

data Constant : Set where
  const : Atom → Constant

data Expr : Set where
  compound  : Operator → Expr → Expr → Expr
  identexpr : Identifier → Expr
  constexpr : Constant → Expr


-- Semantics of source language

data Item : Set where
  item : Atom → Item

data Variable : Set where

-- Environment
itemof   : Constant → Item
itemof = λ _ → item (atom zero)

varof    : Identifier → Variable
varof = {!!}

funcof   : Operator → Item → Item → Item
funcof = λ _ _ z → z

varvalue : Variable → Item
varvalue = λ ()

-- Machine language

data Instruction : Set where
  operate : Operator → Instruction
  loadident : Identifier → Instruction
  loadconst : Constant → Instruction

Mprogram : Set
Mprogram = List Instruction

Stack : Set
Stack = List Item

varval : Variable → Item
varval = λ ()

val : Expr → Item
val (compound op e₁ e₂) = funcof op (val e₂) (val e₂)
val (identexpr id)      = varvalue (varof id)
val (constexpr c)       = itemof c

do' : Instruction → Stack → Stack
do' (operate op) (i₁ ∷ i₂ ∷ st) =
  funcof op i₁ i₂ ∷ st
do' (operate op)   _ = {!!} -- TODO: This function looks partial!
do' (loadident id) st = varvalue (varof id) ∷ st
do' (loadconst c)  st = itemof c ∷ st

-- TODO: remove duplication
concat : List A → List A → List A
concat nil       xs₂ = xs₂
concat (x ∷ xs₁) xs₂ = x ∷ concat xs₁ xs₂
lit : (A → B → B) → List A → B → B
lit f nil      y = y
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
lit-concat-lemma f nil xs₂ y =
  begin
  lit f (concat nil xs₂) y
  ≡⟨⟩ -- By def. of concat
  lit f xs₂ y
  ≡⟨⟩
  lit f nil (lit f xs₂ y) ∎

mpval : Mprogram → Stack → Stack
mpval mp = λ { st → lit do' mp st }

-- Compilation

comp : Expr → Mprogram
comp (compound op e₁ e₂) = operate op ∷ concat (comp e₁) (comp e₂)
comp (identexpr id)      = loadident id ∷ nil
comp (constexpr c)       = loadconst c ∷ nil

theorem1 : {e : Expr} {s : Stack} → mpval (comp e) s ≡ val e ∷ s
theorem1 {e@(compound op e₁ e₂)} {s} =
  let q = theorem1 {e₂} {s}
      p = theorem1 {e₁} {val e₂ ∷ s}
  in
  begin
  mpval (comp e) s -- LHS
  ≡⟨⟩
  lit do' (comp e) s
  ≡⟨⟩
  lit do' (operate op ∷ concat (comp e₁) (comp e₂)) s
  ≡⟨⟩
  do' (operate op) (lit do' (concat (comp e₁) (comp e₂)) s)
  ≡⟨ cong (do' (operate op)) (lit-concat-lemma do' (comp e₁) (comp e₂) s) ⟩
  do' (operate op) (lit do' (comp e₁) (lit do' (comp e₂) s))
  ≡⟨⟩
  do' (operate op) (mpval (comp e₁) (mpval (comp e₂) s)) -- This expression was incorrect in the paper
  ≡⟨ cong (λ x → do' (operate op) (mpval (comp e₁) x)) q ⟩
  do' (operate op) (mpval (comp e₁) (val e₂ ∷ s)) -- This expression was incorrect in the paper
  ≡⟨ cong (do' (operate op)) p ⟩
  do' (operate op) (val e₁ ∷ val e₂ ∷ s)
  ≡⟨⟩
  funcof op (val e₁) (val e₂) ∷ s
  ≡⟨⟩
  val e ∷ s -- RHS
  ∎
theorem1 {e@(identexpr id)} {s} =
  mpval (comp e) s
  ≡⟨⟩
  lit do' (comp e) s
  ≡⟨⟩
  lit do' (loadident id ∷ nil) s
  ≡⟨⟩
  do' (loadident id) s
  ≡⟨⟩
  varvalue (varof id) ∷ s
  ≡⟨⟩
  val e ∷ s ∎
theorem1 {e@(constexpr c)} {s}  =
  mpval (comp e) s
  ≡⟨⟩
  lit do' (comp e) s
  ≡⟨⟩
  lit do' (loadconst c ∷ nil) s
  ≡⟨⟩
  do' (loadconst c) s
  ≡⟨⟩
  itemof c ∷ s
  ≡⟨⟩
  val e ∷ s ∎



