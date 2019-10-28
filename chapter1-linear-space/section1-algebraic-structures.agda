
-- Chapter 1. Linear Space. --
------------------------------


open import Relation.Binary using (Setoid)
open import Level using (_⊔_)

module chapter1-linear-space.section1-algebraic-structures
  {α ℓ} (setoid : Setoid α ℓ) where

open Setoid setoid
  using (_≈_; refl; sym; trans)
  renaming (Carrier to A)

import Algebra.FunctionProperties _≈_ as Properties

-- Section 1. Algebraic structures

-- 1.
open Properties using (Op₁; Op₂; Congruent₁; Congruent₂)
open import Algebra using (Magma)

-- 2.
open Properties using (Commutative)

-- 3.
open Properties using (Associative)
open import Algebra using (Semigroup)

-- 4.
open Properties using (_DistributesOver_)

-- 5.
-- > Summation and multiplication of real numbers is commutative and associative.
--
-- Note: Formalization of real numbers is out of scope of this project.

-- 6.

record Summation : Set (α ⊔ ℓ)  where
  field
    _+_     : Op₂ A
    +-assoc : Associative _+_
    +-comm  : Commutative _+_

record Multiplication : Set (α ⊔ ℓ) where
  field
    _∙_     : Op₂ A
    ∙-assoc : Associative _∙_ 

-- 7-10
-- In the book 7-10 are properties of summation which are just special case of 11-14.

-- 11.
open Properties using (LeftIdentity; RightIdentity)

-- 12.
open Properties using (Identity)
open import Relation.Binary.Reasoning.Setoid setoid
  using (begin_; _≈˘⟨_⟩_; _≈⟨_⟩_; _≡⟨_⟩_; _≡˘⟨_⟩_; _≡⟨⟩_; _∎)

eₗ≈eᵣ : ∀ {eₗ eᵣ _∙_} → LeftIdentity eₗ _∙_ → RightIdentity eᵣ _∙_ → eₗ ≈ eᵣ
eₗ≈eᵣ {eₗ} {eᵣ} {_∙_} eₗ-is-left-identity eᵣ-is-right-identity
  = begin
    eₗ       ≈˘⟨ eᵣ-is-right-identity eₗ ⟩
    eₗ ∙ eᵣ  ≈⟨ eₗ-is-left-identity eᵣ ⟩
    eᵣ
    ∎

-- 13.

open import Algebra.Structures _≈_ using (IsMonoid)

module InverseDefinition {_∙_ e} (isMonoid : IsMonoid _∙_ e) where

  open IsMonoid isMonoid
    using (assoc; identityˡ; identityʳ; ∙-cong; ∙-congˡ; ∙-congʳ)

  _is-left-inverse-of_ : A → A → Set _
  y is-left-inverse-of x = y ∙ x ≈ e

  _is-right-inverse-of_ : A → A → Set _
  y is-right-inverse-of x = x ∙ y ≈ e

-- 14.
  yₗ≈yᵣ : ∀ {yₗ yᵣ x} → (yₗ is-left-inverse-of x) → (yᵣ is-right-inverse-of x) → yₗ ≈ yᵣ
  yₗ≈yᵣ {yₗ} {yᵣ} {x} yₗ∙x≈e x∙yᵣ≈e
    = begin
      yₗ            ≈˘⟨ identityʳ yₗ ⟩
      yₗ ∙ e        ≈⟨ ∙-congˡ (sym x∙yᵣ≈e) ⟩
      yₗ ∙ (x ∙ yᵣ) ≈˘⟨ assoc yₗ x yᵣ ⟩
      (yₗ ∙ x) ∙ yᵣ ≈⟨ ∙-congʳ yₗ∙x≈e ⟩
      e ∙ yᵣ        ≈⟨ identityˡ yᵣ ⟩
      yᵣ
      ∎

-- 15.
  if-yₗ∙x≈e-and-z∙yₗ≈e-then-x∙yₗ≈e :
    ∀ {yₗ x z} →
    yₗ is-left-inverse-of x →
    z is-left-inverse-of yₗ →
    yₗ is-right-inverse-of x
  if-yₗ∙x≈e-and-z∙yₗ≈e-then-x∙yₗ≈e {yₗ} {x} {z} yₗ∙x≈e z∙yₗ≈e
    = begin
      x ∙ yₗ              ≈˘⟨ identityˡ (x ∙ yₗ) ⟩
      e ∙ (x ∙ yₗ)        ≈⟨ ∙-congʳ (sym z∙yₗ≈e) ⟩
      (z ∙ yₗ) ∙ (x ∙ yₗ) ≈⟨ assoc z yₗ (x ∙ yₗ) ⟩
      z ∙ (yₗ ∙ (x ∙ yₗ)) ≈⟨ ∙-congˡ (sym (assoc yₗ x yₗ)) ⟩
      z ∙ ((yₗ ∙ x) ∙ yₗ) ≈⟨ ∙-congˡ (∙-congʳ yₗ∙x≈e) ⟩
      z ∙ (e ∙ yₗ)        ≈⟨ ∙-congˡ (identityˡ yₗ) ⟩
      z ∙ yₗ              ≈⟨ z∙yₗ≈e ⟩
      e
      ∎

-- 16.
open import Algebra.Structures _≈_ using (IsGroup)
open import Algebra using (Group)

-- 17.
open Properties using (LeftInverse)

record IsGroup′ (_∙_ : Op₂ A) (eₗ : A) (_⁻¹ₗ : Op₁ A) : Set (α ⊔ ℓ) where
  field
    ∙-assoc   : Associative _∙_
    ∙-cong    : Congruent₂ _∙_
    identityₗ : LeftIdentity eₗ _∙_
    inverseₗ  : LeftInverse eₗ _⁻¹ₗ _∙_
    ⁻¹ₗ-cong  : Congruent₁ _⁻¹ₗ


IsGroup⇒IsGroup′ : ∀ {_∙_ e _⁻¹} → IsGroup _∙_ e _⁻¹ → IsGroup′ _∙_ e _⁻¹
IsGroup⇒IsGroup′ {_∙_} {e} {_⁻¹} isGroup = record
  { ∙-assoc   = assoc
  ; ∙-cong    = ∙-cong
  ; identityₗ = identityˡ
  ; inverseₗ  = inverseˡ
  ; ⁻¹ₗ-cong  = ⁻¹-cong
  }
  where open IsGroup isGroup

IsGroup′⇒IsGroup : ∀ {_∙_ eₗ _⁻¹ₗ} → IsGroup′ _∙_ eₗ _⁻¹ₗ → IsGroup _∙_ eₗ _⁻¹ₗ
IsGroup′⇒IsGroup {_∙_} {eₗ} {_⁻¹ₗ} isGroup′ = record
  { isMonoid = {!!}
  ; inverse = {!!}
  ; ⁻¹-cong = {!!}
  }
  where open IsGroup′ isGroup′

