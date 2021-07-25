open import Mockingbird.Forest using (Forest)

module Mockingbird.Forest.Combination.Base {b ℓ} (forest : Forest {b} {ℓ}) where

open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred; _∈_)

open Forest forest

private
  variable
    p : Level
    x y z : Bird
    P : Pred Bird p

-- If P is a set of birds, we can think of ⟨ P ⟩ as the set of birds ‘generated
-- by’ P.
data ⟨_⟩ (P : Pred Bird p) : Pred Bird (p ⊔ b ⊔ ℓ) where
  [_] : (x∈P : x ∈ P) → x ∈ ⟨ P ⟩

  _⟨∙⟩_∣_ :
       (x∈⟨P⟩ : x ∈ ⟨ P ⟩)
    → (y∈⟨P⟩ : y ∈ ⟨ P ⟩)
    → (xy≈z : x ∙ y ≈ z)
    → z ∈ ⟨ P ⟩

infixl 6 _⟨∙⟩_
_⟨∙⟩_ : x ∈ ⟨ P ⟩ → y ∈ ⟨ P ⟩ → x ∙ y ∈ ⟨ P ⟩
_⟨∙⟩_ = _⟨∙⟩_∣ refl
