
-- Chapter 1. Linear Space. --
------------------------------


open import Relation.Binary using (Setoid)

module chapter1-linear-space.section1-algebraic-structures
  {α ℓ} (setoid : Setoid α ℓ) where

open Setoid setoid
  using (_≈_; refl; sym; trans)
  renaming (Carrier to A)

import Algebra.FunctionProperties _≈_ as Properties

-- Section 1. Algebraic structures

-- 1.
open Properties using (Op₂; Congruent₂)

-- 2.
open Properties using (Commutative)

-- 3.
open Properties using (Associative)

-- 4.
open Properties using (_DistributesOver_)

-- *5.
-- > Summation and multiplication of real numbers is commutative and associative.
--
-- Note: Formalization of real numbers is out of scope of this project.

-- 6.
-- > Associative and commutative binary operation is usually denoted _+_.
-- > Associative but not necessary commutative binary operation is usualy
-- > denoted _∙_.

-- 7.
open Properties using (Identity)

-- *8.
open import Relation.Binary.Reasoning.Setoid setoid
  using (begin_; _≈˘⟨_⟩_; _≈⟨_⟩_; _≡⟨_⟩_; _≡˘⟨_⟩_; _≡⟨⟩_; _∎)

open import Data.Product  using (_,_)

identity-is-unique : {e₁ e₂ : A} {_∙_ : Op₂ A} → (Identity e₁ _∙_) → (Identity e₂ _∙_) → (e₁ ≈ e₂)
identity-is-unique {e₁} {e₂} {_∙_} (e₁-is-left-identity , _) (_ , e₂-is-right-identity)
  = begin
    e₁       ≈˘⟨  e₂-is-right-identity e₁ ⟩
    e₁ ∙ e₂  ≈⟨ e₁-is-left-identity e₂ ⟩
    e₂
    ∎

-- 9.
open Properties using (Inverse)


