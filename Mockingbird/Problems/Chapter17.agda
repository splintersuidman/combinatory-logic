open import Mockingbird.Forest using (Forest)

-- Gödel's Forest
module Mockingbird.Problems.Chapter17 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; _⇔_; Equivalence; mk⇔)
open import Function.Equivalence.Reasoning renaming (begin_ to ⇔-begin_; _∎ to _⇔-∎)
open import Level using (_⊔_)
open import Relation.Binary using (_Respects_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_)

open Forest forest
open import Mockingbird.Problems.Chapter15 forest using (⇔-¬; ⇔-↯)

record HasMate {s} (Sings : Pred Bird s) : Set (s ⊔ b) where
  field
    _′ : Bird → Bird
    isMate : ∀ {x} y → Sings (x ′ ∙ y) ⇔ (¬ Sings (x ∙ y))

open HasMate ⦃ ... ⦄

record HasAssociate {s} (Sings : Pred Bird s) : Set (s ⊔ b) where
  field
    _* : Bird → Bird
    isAssociate : ∀ {x} y → Sings (x * ∙ y) ⇔ Sings (x ∙ (y ∙ y))

open HasAssociate ⦃ ... ⦄

weakLEM : ∀ {a} (A : Set a) → ¬ ¬ (A ⊎ ¬ A)
weakLEM A ¬[A⊎¬A] =
  let ¬A : ¬ A
      ¬A a = ¬[A⊎¬A] (inj₁ a)

      A⊎¬A : A ⊎ ¬ A
      A⊎¬A = inj₂ ¬A
  in ¬[A⊎¬A] A⊎¬A

module _ {n s} (IsNightingale : Pred Bird n) (Sings : Pred Bird s) (𝒩 : Bird)
         (respects : Sings Respects _≈_)
         (LEM : ∀ x → Sings x ⊎ (¬ Sings x))
         (C₁ : ∀ {x} → IsNightingale x → Sings x)
         ⦃ C₂ : HasMate Sings ⦄
         ⦃ C₃ : HasAssociate Sings ⦄
         (C₄ : ∀ x → Sings (𝒩 ∙ x) ⇔ IsNightingale x) where

  private
    doubleNegation : ∀ x → ¬ ¬ Sings x → Sings x
    doubleNegation x ¬¬x-sings with LEM x
    ... | inj₁ x-sings = x-sings
    ... | inj₂ ¬x-sings = ⊥-elim $ ¬¬x-sings ¬x-sings

    doubleNegation-⇔ : ∀ x → (¬ ¬ Sings x) ⇔ Sings x
    doubleNegation-⇔ x = mk⇔ (doubleNegation x) (λ x-sings ¬x-sings → ¬x-sings x-sings)

  problem₁ : ∃[ 𝒢 ] (Sings 𝒢 × ¬ IsNightingale 𝒢)
  problem₁ = (𝒢 , conclusion)
    where
      𝒩′ = 𝒩 ′
      𝒩′* = 𝒩′ *
      𝒢 = 𝒩′* ∙ 𝒩′*

      𝒢-sings⇔¬𝒩𝒢-sings : Sings 𝒢 ⇔ (¬ Sings (𝒩 ∙ 𝒢))
      𝒢-sings⇔¬𝒩𝒢-sings = ⇔-begin
        Sings 𝒢                   ⇔⟨⟩
        Sings (𝒩′* ∙ 𝒩′*)         ⇔⟨ isAssociate 𝒩′* ⟩
        Sings (𝒩′ ∙ (𝒩′* ∙ 𝒩′*))  ⇔⟨⟩
        Sings (𝒩′ ∙ 𝒢)            ⇔⟨ isMate 𝒢 ⟩
        (¬ Sings (𝒩 ∙ 𝒢))         ⇔-∎

      ¬𝒢-sings⇔𝒢-isNightingale : (¬ Sings 𝒢) ⇔ IsNightingale 𝒢
      ¬𝒢-sings⇔𝒢-isNightingale = ⇔-begin
        ¬ Sings 𝒢          ⇔⟨ ⇔-¬ 𝒢-sings⇔¬𝒩𝒢-sings ⟩
        ¬ ¬ Sings (𝒩 ∙ 𝒢)  ⇔⟨ doubleNegation-⇔ $ 𝒩 ∙ 𝒢 ⟩
        Sings (𝒩 ∙ 𝒢)      ⇔⟨ C₄ 𝒢 ⟩
        IsNightingale 𝒢    ⇔-∎

      𝒢-sings⇔¬𝒢-isNightingale : Sings 𝒢 ⇔ (¬ IsNightingale 𝒢)
      𝒢-sings⇔¬𝒢-isNightingale = ⇔-begin
        Sings 𝒢              ⇔˘⟨ doubleNegation-⇔ 𝒢 ⟩
        ¬ ¬ Sings 𝒢          ⇔⟨ ⇔-¬ ¬𝒢-sings⇔𝒢-isNightingale ⟩
        (¬ IsNightingale 𝒢)  ⇔-∎

      conclusion : Sings 𝒢 × ¬ IsNightingale 𝒢
      conclusion with LEM 𝒢
      ... | inj₁ 𝒢-sings = (𝒢-sings , Equivalence.f 𝒢-sings⇔¬𝒢-isNightingale 𝒢-sings)
      ... | inj₂ ¬𝒢-sings = ⊥-elim $ ¬𝒢-sings $ C₁ $ Equivalence.f ¬𝒢-sings⇔𝒢-isNightingale ¬𝒢-sings

  problem₂ : ∃[ 𝒢 ] (Sings 𝒢 × ¬ IsNightingale 𝒢)
  problem₂ = (𝒢 , conclusion)
    where
      𝒩* = 𝒩 *
      𝒩*′ = 𝒩* ′
      𝒢 = 𝒩*′ ∙ 𝒩*′

      -- Note: this proof (and the definition of 𝒢) is the only difference to
      -- the proof of problem 1.
      𝒢-sings⇔¬𝒩𝒢-sings : Sings 𝒢 ⇔ (¬ Sings (𝒩 ∙ 𝒢))
      𝒢-sings⇔¬𝒩𝒢-sings = ⇔-begin
        Sings 𝒢 ⇔⟨⟩
        Sings (𝒩*′ ∙ 𝒩*′)          ⇔⟨ isMate 𝒩*′ ⟩
        ¬ Sings (𝒩* ∙ 𝒩*′)         ⇔⟨ ⇔-¬ $ isAssociate 𝒩*′ ⟩
        ¬ Sings (𝒩 ∙ (𝒩*′ ∙ 𝒩*′))  ⇔⟨⟩
        (¬ Sings (𝒩 ∙ 𝒢))          ⇔-∎

      ¬𝒢-sings⇔𝒢-isNightingale : (¬ Sings 𝒢) ⇔ IsNightingale 𝒢
      ¬𝒢-sings⇔𝒢-isNightingale = ⇔-begin
        ¬ Sings 𝒢          ⇔⟨ ⇔-¬ 𝒢-sings⇔¬𝒩𝒢-sings ⟩
        ¬ ¬ Sings (𝒩 ∙ 𝒢)  ⇔⟨ doubleNegation-⇔ $ 𝒩 ∙ 𝒢 ⟩
        Sings (𝒩 ∙ 𝒢)      ⇔⟨ C₄ 𝒢 ⟩
        IsNightingale 𝒢    ⇔-∎

      𝒢-sings⇔¬𝒢-isNightingale : Sings 𝒢 ⇔ (¬ IsNightingale 𝒢)
      𝒢-sings⇔¬𝒢-isNightingale = ⇔-begin
        Sings 𝒢              ⇔˘⟨ doubleNegation-⇔ 𝒢 ⟩
        ¬ ¬ Sings 𝒢          ⇔⟨ ⇔-¬ ¬𝒢-sings⇔𝒢-isNightingale ⟩
        (¬ IsNightingale 𝒢)  ⇔-∎

      conclusion : Sings 𝒢 × ¬ IsNightingale 𝒢
      conclusion with LEM 𝒢
      ... | inj₁ 𝒢-sings = (𝒢-sings , Equivalence.f 𝒢-sings⇔¬𝒢-isNightingale 𝒢-sings)
      ... | inj₂ ¬𝒢-sings = ⊥-elim $ ¬𝒢-sings $ C₁ $ Equivalence.f ¬𝒢-sings⇔𝒢-isNightingale ¬𝒢-sings

  _Represents_ : ∀ {r} → (A : Bird) → (𝒮 : Pred Bird r) → Set (b ⊔ s ⊔ r)
  A Represents 𝒮 = ∀ x → Sings (A ∙ x) ⇔ x ∈ 𝒮

  IsSociety : ∀ {r} → (𝒮 : Pred Bird r) → Set (b ⊔ s ⊔ r)
  IsSociety 𝒮 = ∃[ A ] A Represents 𝒮

  _ : IsSociety IsNightingale
  _ = (𝒩 , C₄)

  problem₃ : ¬ IsSociety Sings
  problem₃ 𝒮@(A , A-represents) =
    let A′ = A ′
        A′* = A′ *

        𝒮ᶜ : IsSociety λ x → ¬ Sings x
        𝒮ᶜ =
          ( A′
          , λ x → ⇔-begin
              Sings (A′ ∙ x)   ⇔⟨ isMate x ⟩
              ¬ Sings (A ∙ x)  ⇔⟨ ⇔-¬ $ A-represents x ⟩
              (¬ Sings x)      ⇔-∎
          )

        A′*A′*-sings⇔¬A′*A′*-sings : Sings (A′* ∙ A′*) ⇔ (¬ Sings (A′* ∙ A′*))
        A′*A′*-sings⇔¬A′*A′*-sings = ⇔-begin
          Sings (A′* ∙ A′*)         ⇔⟨ isAssociate A′* ⟩
          Sings (A′ ∙ (A′* ∙ A′*))  ⇔⟨ proj₂ 𝒮ᶜ (A′* ∙ A′*) ⟩
          (¬ Sings (A′* ∙ A′*))     ⇔-∎

    in ⇔-↯ A′*A′*-sings⇔¬A′*A′*-sings
