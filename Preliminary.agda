{-# OPTIONS --prop --safe #-}

module Preliminary where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)

private variable
    ℓ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ' ℓ₁' ℓ₂' ℓ₃' ℓ₄' ℓ₅' ℓ₆' ℓ₇' ℓ₈' : Level

id : {A : Set ℓ} -> A -> A
id a = a

_∘_ : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
    -> (B -> C) -> (A -> B) -> A -> C
f ∘ g = \ z -> f (g z)

idP : {A : Prop ℓ} -> A -> A
idP a = a

_↣_ : {A : Prop ℓ₁} {B : Prop ℓ₂} {C : Prop ℓ₃}
    -> (A -> B) -> (B -> C) -> A -> C
f ↣ g = \ z -> g (f z)

infixl 8 _∧_ _*_
infixl 7 _∨_ _⊎_

data ⊥ : Prop where
record ⊤ : Prop where
    constructor ⋆

record _∧_ (P : Prop ℓ) (Q : Prop ℓ') : Prop (ℓ ⊔ ℓ') where
    constructor [_,_]
    field
        π₁ : P
        π₂ : Q

-- Pairs, the × notation is reserved for PSet products
record _*_ (P : Set ℓ) (Q : Set ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _,_
    field
        proj₁ : P
        proj₂ : Q

open _∧_ public
open _*_ public

data _∨_ (P : Prop ℓ) (Q : Prop ℓ') : Prop (ℓ ⊔ ℓ') where
    ι₁ : P -> P ∨ Q
    ι₂ : Q -> P ∨ Q

data _⊎_ (P : Set ℓ) (Q : Set ℓ') : Set (ℓ ⊔ ℓ') where
    inj₁ : P -> P ⊎ Q
    inj₂ : Q -> P ⊎ Q

data Empty {ℓ} : Set ℓ where
magic : ∀ {A : Set ℓ} -> Empty {ℓ'} -> A
magic ()
magicP : ∀ {A : Prop ℓ} -> Empty {ℓ'} -> A
magicP ()

data Bool {ℓ} : Set ℓ where
    true : Bool
    false : Bool

Bool-decidable : ∀ (a b : Bool {ℓ}) -> (a ≡ b) ⊎ (a ≡ b -> Empty {ℓ'})
Bool-decidable true true = inj₁ refl
Bool-decidable true false = inj₂ \ ()
Bool-decidable false true = inj₂ \ ()
Bool-decidable false false = inj₁ refl

data ∃ (A : Set ℓ) (P : A -> Prop ℓ') : Prop (ℓ ⊔ ℓ') where
    ⟨_,_⟩ : (a : A) -> P a -> ∃ A P

∃-syntax = ∃
∀-syntax : (A : Set ℓ) (P : A -> Prop ℓ') -> Prop (ℓ ⊔ ℓ')
∀-syntax A P = (x : A) -> P x
syntax ∃-syntax A (\ a -> P) = ∃⟨ a ∶ A ⟩ P
syntax ∀-syntax A (\ a -> P) = ∀⟨ a ∶ A ⟩ P

data ∥_∥ (A : Set ℓ) : Prop ℓ where
    tt : A -> ∥ A ∥
