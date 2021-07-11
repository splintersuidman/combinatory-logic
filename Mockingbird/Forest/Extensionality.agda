open import Mockingbird.Forest using (Forest)

module Mockingbird.Forest.Extensionality {b ℓ} (forest : Forest {b} {ℓ}) where

open import Algebra using (RightCongruent)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Level using (_⊔_)

open Forest forest

-- TODO: if the arguments to the predicates is{Mockingbird,Thrush,Cardinal,...}
-- are made implicit, then x can be implicit too.
Similar : Rel Bird (b ⊔ ℓ)
Similar A₁ A₂ = ∀ x → A₁ ∙ x ≈ A₂ ∙ x

infix 4 _≋_
_≋_ = Similar

-- A forest is called extensional if similarity implies equality.
IsExtensional : Set (b ⊔ ℓ)
IsExtensional = ∀ {A₁ A₂} → A₁ ≋ A₂ → A₁ ≈ A₂

-- A record to be used as an instance argument.
record Extensional : Set (b ⊔ ℓ) where
  field
    ext : IsExtensional

open Extensional ⦃ ... ⦄ public

ext′ : ⦃ _ : Extensional ⦄ → ∀ {A₁ A₂} → (∀ {x} → A₁ ∙ x ≈ A₂ ∙ x) → A₁ ≈ A₂
ext′ A₁≋A₂ = ext λ _ → A₁≋A₂

-- Similarity is an equivalence relation.
≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = record
  { refl = λ _ → refl
  ; sym = λ x≋y z → sym (x≋y z)
  ; trans = λ x≋y y≋z w → trans (x≋y w) (y≋z w)
  }

≋-∙-congʳ : RightCongruent _≋_ _∙_
≋-∙-congʳ {w} {x} {y} x≋y = λ _ → ∙-congʳ (x≋y w)
