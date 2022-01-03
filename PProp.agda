{-# OPTIONS --prop --safe --postfix-projections --overlapping-instances #-}

module PProp where
-- Defines PProp, the central tool for the antithesis translation.
-- The extra "P" may stand for "polarized", "paired", or just
-- "double Prop", pick your favourite.

-- On precedences:
-- - The operators on usual Prop takes a precedence of < 15.
-- - The operators on PProp takes ≥ 15.
-- - The operators on proof terms takes ≥ 10
infix 0 _☯_
infixr 20 ¬_
infixr 15 _⟶_
infixl 19 _⊗_

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Preliminary
private variable
    ℓ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ' ℓ₁' ℓ₂' ℓ₃' ℓ₄' ℓ₅' ℓ₆' ℓ₇' ℓ₈' : Level

-- A PProp, apart from universe level issues, is simply two propositions.
record PProp ℓ ℓ' : Set (lsuc (ℓ ⊔ ℓ')) where
    field
        Aff : Prop ℓ  -- Thesis
        Ref : Prop ℓ' -- Antithesis
open PProp
-- The Aff part denotes "how to affirm this PProp", whereas
-- the Ref part denotes "how to refute this PProp".
-- Of course, simply bundling any two propositions together doesn't
-- really buy us anything. Therefore, we impose a third component
-- in this definition: Aff and Ref must be in conflict. In the spirit
-- of Hegel, we call these three Thesis-Antithesis-Synthesis.

-- The Synthesis part is declared as a typeclass for convenience.
record Syn (P : PProp ℓ ℓ') : Prop (ℓ ⊔ ℓ') where
    field Chu : Aff P -> Ref P -> ⊥
open Syn ⦃...⦄

-- A pretty taichi symbol for that.
_☯_ : {P : PProp ℓ ℓ'} -> ⦃ Syn P ⦄ -> Aff P -> Ref P -> ⊥
_☯_ = Chu
{-# INLINE _☯_ #-}

-- Before we plunge in the development, let's note our choice of ⊥ here.
-- Actually, it isn't necessary to use ⊥ for it to work: anything would
-- work here! Such a construction is called Chu- or Dialectica-construction.
-- If we choose ⊥, then these two constructions become the same. It also makes
-- a lot of additional complications disappear.

private variable
    P : PProp ℓ₁ ℓ₂
    Q : PProp ℓ₃ ℓ₄
    R : PProp ℓ₅ ℓ₆
    S : PProp ℓ₇ ℓ₈

-- Now we can start defining simple propositions.
𝕋 : PProp lzero lzero
𝕋 .Aff = ⊤
𝕋 .Ref = ⊥
instance
    Syn𝕋 : Syn 𝕋
    Syn𝕋 .Chu _ ()

-- Every Prop can be made into a PProp.
-- This resembles the ! (bang / of course) modality in linear logic.
bang : Prop ℓ -> PProp ℓ ℓ
bang P .Aff = P
bang P .Ref = P -> ⊥
instance
    SynBang : {P : Prop ℓ} -> Syn (bang P)
    SynBang .Chu p p̅ = p̅ p

-- Negation amounts to switching the affirmation and refutation part.
¬_ : PProp ℓ₁ ℓ₂ -> PProp ℓ₂ ℓ₁
(¬ P) .Aff = P .Ref
(¬ P) .Ref = P .Aff

-- Double negation for free!
_ : P ≡ ¬ ¬ P
_ = refl

-- ... But that comes at a cost. Since ¬ ¬ P computes to P,
-- this causes Agda to loop if it were declared as an instance:
Syn¬ : (P : PProp ℓ₁ ℓ₂) -> ⦃ Syn P ⦄ -> Syn (¬ P)
Syn¬ P .Chu p p̅ = p̅ ☯ p
-- Therefore it should only be used locally, by declaring the argument
-- P explicitly. The canonical usage:
--   let instance _ = Syn¬ P in ...

𝔽 : PProp lzero lzero
𝔽 = ¬ 𝕋
instance
    Syn𝔽 : Syn 𝔽
    Syn𝔽 = Syn¬ 𝕋

-- But apart from 𝕋 and 𝔽, we have more bizarre propositions:
𝕀 : PProp lzero lzero
𝕀 .Aff = ⊥
𝕀 .Ref = ⊥
instance
    Syn𝕀 : Syn 𝕀
    Syn𝕀 .Chu () ()
-- This is neither provable nor refutable!

-- This is "the" implication that is the most useful in practice.
_⟶_ : PProp ℓ₁ ℓ₂ -> PProp ℓ₃ ℓ₄ -> PProp (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) (ℓ₁ ⊔ ℓ₄)
(P ⟶ Q) .Aff = (Aff P -> Aff Q) ∧ (Ref Q -> Ref P)
(P ⟶ Q) .Ref = Aff P ∧ Ref Q

instance
    Syn*⟶ : ⦃ Syn P ⦄ -> Syn (P ⟶ Q)
    Syn*⟶ .Chu [ a , b ] [ c , d ] = c ☯ b d

    Syn⟶* : ⦃ Syn Q ⦄ -> Syn (P ⟶ Q)
    Syn⟶* .Chu [ a , b ] [ c , d ] = a c ☯ d
    -- These arn't reported as overlapping instances since _⟶_ is
    -- not a rigid term. Also, since we are working over Prop, these
    -- two instances are considered equal.

-- In category speak, we can make PProp a category, and treat each proof of
-- Aff (P ⟶ Q) as an arrow from P to Q. Then _⟶_ should become the
-- "internal hom" of this category.

-- The definition of internal hom says that, given a category with a monoidal
-- product _⊠_, the internal hom is an operation that curries over it:
--   (P ⊠ Q) ⟶ R ≃ P ⟶ (Q ⟶ R).
-- Here we define the internal hom in terms of the monoidal product, however,
-- in practice (such as here), there is a hom-like concept that comes up first,
-- and then we search for the corresponding monoidal product.

-- If you are familiar with linear algebra, then here's a quick example.
-- Consider the set of linear functions between two vector spaces V -> W. Then
-- these functions themselves form a vector space. We would naturally expect that
-- to be the internal hom. What would be the monoidal product? It turns out to
-- be the tensor product of vector spaces.

-- What is the monoidal product corresponding to this internal hom?
-- Thanks to the Chu construction, we can do this neatly:
_⊗_ : PProp ℓ₁ ℓ₂ -> PProp ℓ₃ ℓ₄ -> PProp (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
P ⊗ Q = ¬ (P ⟶ ¬ Q)

-- 𝔽 acts as the "dualizing object" of _⟶_, i.e. _⟶ 𝔽 is the same as ¬_.
-- ...

