module Mockingbird.Forest.Base where

open import Algebra using (Op₂; Congruent₂; LeftCongruent; RightCongruent)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Nullary using (¬_)

record IsForest {b ℓ} (Bird : Set b) (_≈_ : Rel Bird ℓ) (_∙_ : Op₂ Bird) : Set (b ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_
    cong : Congruent₂ _≈_ _∙_

  open IsEquivalence isEquivalence public

  setoid : Setoid b ℓ
  setoid = record { isEquivalence = isEquivalence }

  congˡ : LeftCongruent _≈_ _∙_
  congˡ A≈B = cong refl A≈B

  congʳ : RightCongruent _≈_ _∙_
  congʳ A≈B = cong A≈B refl

record Forest {b ℓ} : Set (lsuc (b ⊔ ℓ)) where
  infix  4 _≈_
  infixl 6 _∙_

  field
    Bird : Set b
    _≈_ : Rel Bird ℓ
    _∙_ : Op₂ Bird
    isForest : IsForest Bird _≈_ _∙_

  _≉_ : Rel Bird ℓ
  x ≉ y = ¬ (x ≈ y)

  open IsForest isForest public

  import Relation.Binary.Reasoning.Base.Single _≈_ refl trans as Base
  open Base using (begin_; _∎) public

  infixr 2 _≈⟨⟩_ step-≈ step-≈˘

  _≈⟨⟩_ : ∀ x {y} → x Base.IsRelatedTo y → x Base.IsRelatedTo y
  _ ≈⟨⟩ x≈y = x≈y

  step-≈ = Base.step-∼
  syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

  step-≈˘ : ∀ x {y z} → y Base.IsRelatedTo z → y ≈ x → x Base.IsRelatedTo z
  step-≈˘ x y∼z y≈x = x ≈⟨ sym y≈x ⟩ y∼z
  syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z
