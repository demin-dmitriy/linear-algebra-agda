
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
open Properties using (Op₁; Op₂; Congruent₁; Congruent₂; LeftCongruent; RightCongruent)
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

module [13-14] {_∙_ e} (isMonoid : IsMonoid _∙_ e) where

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
-- In the book e is identity. However left identity is enough. Moreover it's going to be useful
-- later in (17).

module [15]
  {_∙_ e}
  (assoc : Associative _∙_)
  (∙-cong : Congruent₂ _∙_)
  (identityₗ : LeftIdentity e _∙_) where

  ∙-congᵣ : RightCongruent _∙_
  ∙-congᵣ = λ x → ∙-cong x refl

  ∙-congₗ : LeftCongruent _∙_
  ∙-congₗ = ∙-cong refl

  if-yₗ∙x≈e-and-z∙yₗ≈e-then-x∙yₗ≈e : ∀ {yₗ x z} → yₗ ∙ x ≈ e → z ∙ yₗ ≈ e → x ∙ yₗ ≈ e
  if-yₗ∙x≈e-and-z∙yₗ≈e-then-x∙yₗ≈e {yₗ} {x} {z} yₗ∙x≈e z∙yₗ≈e
    = begin
      x ∙ yₗ              ≈˘⟨ identityₗ (x ∙ yₗ) ⟩
      e ∙ (x ∙ yₗ)        ≈⟨ ∙-congᵣ (sym z∙yₗ≈e) ⟩
      (z ∙ yₗ) ∙ (x ∙ yₗ) ≈⟨ assoc z yₗ (x ∙ yₗ) ⟩
      z ∙ (yₗ ∙ (x ∙ yₗ)) ≈⟨ ∙-congₗ (sym (assoc yₗ x yₗ)) ⟩
      z ∙ ((yₗ ∙ x) ∙ yₗ) ≈⟨ ∙-congₗ (∙-congᵣ yₗ∙x≈e) ⟩
      z ∙ (e ∙ yₗ)        ≈⟨ ∙-congₗ (identityₗ yₗ) ⟩
      z ∙ yₗ              ≈⟨ z∙yₗ≈e ⟩
      e
      ∎

-- 16.
open import Algebra.Structures _≈_ using (IsGroup)
open import Algebra using (Group)

-- 17.
open Properties using (LeftInverse; RightInverse)
open import Data.Product using(_,_)

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
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence =  Setoid.isEquivalence setoid
        ; ∙-cong =  ∙-cong
        }
      ; assoc = ∙-assoc
      }
    ; identity = identityₗ , eₗ≡eᵣ
    }
  ; inverse = inverseₗ , inverseᵣ
  ; ⁻¹-cong = ⁻¹ₗ-cong
  }
  where
    open IsGroup′ isGroup′
    open [15] ∙-assoc ∙-cong identityₗ

    inverseᵣ : RightInverse eₗ _⁻¹ₗ _∙_
    inverseᵣ x = if-yₗ∙x≈e-and-z∙yₗ≈e-then-x∙yₗ≈e (inverseₗ x) (inverseₗ (x ⁻¹ₗ))

    -- For some reason in the book it is ignored that this statement needs a proof.
    -- This seems like an oversight, but it's easy to come up with a proof by ourselves.
    eₗ≡eᵣ : RightIdentity eₗ _∙_
    eₗ≡eᵣ x =
      begin
      x ∙ eₗ            ≈⟨ ∙-congₗ (sym (inverseₗ x)) ⟩
      x ∙ ((x ⁻¹ₗ) ∙ x) ≈⟨ sym (∙-assoc x (x ⁻¹ₗ) x)  ⟩
      (x ∙ (x ⁻¹ₗ)) ∙ x ≈⟨ ∙-congᵣ (inverseᵣ x) ⟩
      eₗ ∙ x            ≈⟨ identityₗ x ⟩
      x
      ∎

-- 18.

-- TODO

-- 19.
open import Algebra.Structures _≈_ using (IsAbelianGroup)
open import Algebra using (AbelianGroup)

-- 20.

-- TODO

-- 21.

-- TODO

-- 22.
open import Algebra.Structures _≈_ using (IsRing)
open import Algebra using (Ring)

-- 23.
open import Algebra.Structures _≈_ using (IsCommutativeRing)
open import Algebra using (CommutativeRing)

-- TODO

-- 24.

-- TODO

-- 25.

-- TODO

-- 26.

-- TODO
