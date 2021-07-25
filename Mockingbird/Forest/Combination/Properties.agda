open import Mockingbird.Forest using (Forest)

module Mockingbird.Forest.Combination.Properties {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Product using (_×_; _,_)
open import Relation.Binary using (_Respects_)
open import Relation.Unary using (Pred; _∈_; _⊆_; ∅; _∩_)
open import Level using (Level; _⊔_)

open Forest forest

open import Mockingbird.Forest.Combination.Base forest

private
  variable
    x y z : Bird
    p : Level
    P Q : Pred Bird p

subst : P Respects _≈_ → x ≈ y → x ∈ ⟨ P ⟩ → y ∈ ⟨ P ⟩
subst respects x≈y [ x∈P ] = [ respects x≈y x∈P ]
subst respects x≈y (x₁∈⟨P⟩ ⟨∙⟩ x₂∈⟨P⟩ ∣ x₁x₂≈x) = x₁∈⟨P⟩ ⟨∙⟩ x₂∈⟨P⟩ ∣ trans x₁x₂≈x x≈y

subst′ : P Respects _≈_ → y ≈ x → x ∈ ⟨ P ⟩ → y ∈ ⟨ P ⟩
subst′ respects y≈x = subst respects (sym y≈x)

-- TODO: maybe lift ∅ to an arbitrary level p
⟨∅⟩ : ⟨ ∅ ⟩ ⊆ ∅
⟨∅⟩ (X ⟨∙⟩ Y ∣ xy≈z) = ⟨∅⟩ X

⟨_⟩⊆⟨_⟩ : ∀ {p} (P Q : Pred Bird p) → P ⊆ Q → ⟨ P ⟩ ⊆ ⟨ Q ⟩
⟨ P ⟩⊆⟨ Q ⟩ P⊆Q [ x∈P ] = [ P⊆Q x∈P ]
⟨ P ⟩⊆⟨ Q ⟩ P⊆Q (x∈⟨P⟩ ⟨∙⟩ y∈⟨P⟩ ∣ xy≈z) = ⟨ P ⟩⊆⟨ Q ⟩ P⊆Q x∈⟨P⟩ ⟨∙⟩ ⟨ P ⟩⊆⟨ Q ⟩ P⊆Q y∈⟨P⟩ ∣ xy≈z

weaken : ∀ {p} {P Q : Pred Bird p} → P ⊆ Q → ⟨ P ⟩ ⊆ ⟨ Q ⟩
weaken {P = P} {Q} = ⟨ P ⟩⊆⟨ Q ⟩

⟨_∩_⟩ : ∀ {p} (P Q : Pred Bird p) → ⟨ (P ∩ Q) ⟩ ⊆ ⟨ P ⟩ ∩ ⟨ Q ⟩
⟨ P ∩ Q ⟩ [ (x∈P , x∈Q) ] = ([ x∈P ] , [ x∈Q ])
⟨ P ∩ Q ⟩ (_⟨∙⟩_∣_ {x} {y} {z} x∈⟨P∩Q⟩ y∈⟨P∩Q⟩ xy≈z) =
  let (x∈⟨P⟩ , x∈⟨Q⟩) = ⟨_∩_⟩ P Q x∈⟨P∩Q⟩
      (y∈⟨P⟩ , y∈⟨Q⟩) = ⟨_∩_⟩ P Q y∈⟨P∩Q⟩
  in (x∈⟨P⟩ ⟨∙⟩ y∈⟨P⟩ ∣ xy≈z , x∈⟨Q⟩ ⟨∙⟩ y∈⟨Q⟩ ∣ xy≈z)

-- NOTE: the inclusion ⟨P⟩ ∩ ⟨Q⟩ ⊆ ⟨P ∩ Q⟩ does not hold for all P and Q; let
-- for example P = {S, K}, Q = {I}, then SKK = I ∈ ⟨P⟩ ∩ ⟨Q⟩, but P ∩ Q = ∅, and
-- hence SKK = I ∉ ⟨P ∩ Q⟩.
-- TODO: formalise
