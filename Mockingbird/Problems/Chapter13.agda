open import Mockingbird.Forest using (Forest)

-- A Gallery of Sage Birds
module Mockingbird.Problems.Chapter13 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Function using (_$_)
open import Data.Product using (proj₂)

open import Mockingbird.Forest.Birds forest
import Mockingbird.Problems.Chapter09 forest as Chapter₉
import Mockingbird.Problems.Chapter10 forest as Chapter₁₀
import Mockingbird.Problems.Chapter11 forest as Chapter₁₁
import Mockingbird.Problems.Chapter12 forest as Chapter₁₂

open Forest forest

problem₁ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasMockingbird ⦄ ⦃ _ : HasRobin ⦄ → HasSageBird
problem₁ = record
  { Θ = B ∙ M ∙ (R ∙ M ∙ B)
  ; isSageBird = λ x → begin
      x ∙ (B ∙ M ∙ (R ∙ M ∙ B) ∙ x)  ≈⟨ ∙-congˡ lemma ⟩
      x ∙ (M ∙ (B ∙ x ∙ M))          ≈⟨ isFond ⟩
      M ∙ (B ∙ x ∙ M)                ≈˘⟨ lemma ⟩
      B ∙ M ∙ (R ∙ M ∙ B) ∙ x        ∎
  } where
  isFond = λ {x} → proj₂ (Chapter₁₁.problem₂ x)

  lemma : ∀ {x} → B ∙ M ∙ (R ∙ M ∙ B) ∙ x ≈ M ∙ (B ∙ x ∙ M)
  lemma {x} = begin
    B ∙ M ∙ (R ∙ M ∙ B) ∙ x  ≈⟨ isBluebird M (R ∙ M ∙ B) x ⟩
    M ∙ (R ∙ M ∙ B ∙ x)      ≈⟨ ∙-congˡ $ isRobin M B x ⟩
    M ∙ (B ∙ x ∙ M)          ∎

problem₂ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasMockingbird ⦄ ⦃ _ : HasCardinal ⦄ → HasSageBird
problem₂ = record
  { Θ = B ∙ M ∙ (C ∙ B ∙ M)
  ; isSageBird = λ x → begin
      x ∙ (B ∙ M ∙ (C ∙ B ∙ M) ∙ x)  ≈⟨ ∙-congˡ lemma ⟩
      x ∙ (M ∙ (B ∙ x ∙ M))          ≈⟨ isFond ⟩
      M ∙ (B ∙ x ∙ M)                ≈˘⟨ lemma ⟩
      B ∙ M ∙ (C ∙ B ∙ M) ∙ x        ∎
  } where
  isFond = λ {x} → proj₂ (Chapter₁₁.problem₂ x)

  lemma : ∀ {x} → B ∙ M ∙ (C ∙ B ∙ M) ∙ x ≈ M ∙ (B ∙ x ∙ M)
  lemma {x} = begin
    B ∙ M ∙ (C ∙ B ∙ M) ∙ x  ≈⟨ isBluebird M (C ∙ B ∙ M) x ⟩
    M ∙ (C ∙ B ∙ M ∙ x)      ≈⟨ ∙-congˡ $ isCardinal B M x ⟩
    M ∙ (B ∙ x ∙ M)          ∎

problem₃ : ⦃ _ : HasMockingbird ⦄ ⦃ _ : HasBluebird ⦄ ⦃ _ : HasLark ⦄ → HasSageBird
problem₃ = record
  { Θ = B ∙ M ∙ L
  ; isSageBird = isSageBird ⦃ Chapter₁₀.hasSageBird ⦄
  } where instance hasComposition = Chapter₁₁.problem₁

problem₄ : ⦃ _ : HasMockingbird ⦄ ⦃ _ : HasBluebird ⦄ ⦃ _ : HasWarbler ⦄ → HasSageBird
problem₄ = record
  { Θ = B ∙ M ∙ (B ∙ W ∙ B)
  ; isSageBird = isSageBird ⦃ problem₃ ⦄
  } where instance hasLark = Chapter₁₂.problem₃

problem₆ : ⦃ _ : HasQueerBird ⦄ ⦃ _ : HasLark ⦄ ⦃ _ : HasWarbler ⦄ → HasSageBird
problem₆ = record
  { Θ = W ∙ (Q ∙ L ∙ (Q ∙ L))
  ; isSageBird = λ x → begin
      x ∙ (W ∙ (Q ∙ L ∙ (Q ∙ L)) ∙ x)  ≈⟨ ∙-congˡ lemma ⟩
      x ∙ (L ∙ x ∙ (L ∙ x))            ≈⟨ isFond ⟩
      L ∙ x ∙ (L ∙ x)                  ≈˘⟨ lemma ⟩
      W ∙ (Q ∙ L ∙ (Q ∙ L)) ∙ x        ∎
  } where
  isFond = λ {x} → proj₂ (Chapter₉.problem₂₅ x)

  lemma : ∀ {x} → W ∙ (Q ∙ L ∙ (Q ∙ L)) ∙ x ≈ L ∙ x ∙ (L ∙ x)
  lemma {x} = begin
      W ∙ (Q ∙ L ∙ (Q ∙ L)) ∙ x  ≈⟨ isWarbler (Q ∙ L ∙ (Q ∙ L)) x ⟩
      Q ∙ L ∙ (Q ∙ L) ∙ x ∙ x    ≈⟨ ∙-congʳ $ isQueerBird L (Q ∙ L) x ⟩
      Q ∙ L ∙ (L ∙ x) ∙ x        ≈⟨ isQueerBird L (L ∙ x) x ⟩
      L ∙ x ∙ (L ∙ x)            ∎
  

problem₅ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasCardinal ⦄ ⦃ _ : HasWarbler ⦄ → HasSageBird
problem₅ = problem₆
  where
    instance
      hasQueerBird = Chapter₁₁.problem₃₇′
      hasLark = Chapter₁₂.problem₃

problem₇ = problem₅

problem₈ : ⦃ _ : HasMockingbird ⦄ ⦃ _ : HasQueerBird ⦄ → HasSageBird
problem₈ = record
  { Θ = Q ∙ (Q ∙ M) ∙ M
  ; isSageBird = λ x → sym $ begin
      Q ∙ (Q ∙ M) ∙ M ∙ x        ≈⟨ isQueerBird (Q ∙ M) M x ⟩
      M ∙ (Q ∙ M ∙ x)            ≈⟨ isMockingbird (Q ∙ M ∙ x) ⟩
      Q ∙ M ∙ x ∙ (Q ∙ M ∙ x)    ≈⟨ isQueerBird M x (Q ∙ M ∙ x) ⟩
      x ∙ (M ∙ (Q ∙ M ∙ x))      ≈˘⟨ ∙-congˡ $ isQueerBird (Q ∙ M) M x ⟩
      x ∙ (Q ∙ (Q ∙ M) ∙ M ∙ x)  ∎
  }

-- TODO: formalise regularity.

problem₉ : ⦃ _ : HasStarling ⦄ ⦃ _ : HasLark ⦄ → HasSageBird
problem₉ = record
  { Θ = S ∙ L ∙ L
  ; isSageBird = λ x → begin
      x ∙ (S ∙ L ∙ L ∙ x)    ≈⟨ ∙-congˡ $ isStarling L L x ⟩
      x ∙ (L ∙ x ∙ (L ∙ x))  ≈⟨ isFond ⟩
      L ∙ x ∙ (L ∙ x)        ≈˘⟨ isStarling L L x ⟩
      S ∙ L ∙ L ∙ x          ∎
  } where
  isFond = λ {x} → proj₂ (Chapter₉.problem₂₅ x)

problem₁₀ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasWarbler ⦄ ⦃ _ : HasStarling ⦄ → HasSageBird
problem₁₀ = record
  { Θ = W ∙ S ∙ (B ∙ W ∙ B)
  ; isSageBird = λ x → begin
      x ∙ (W ∙ S ∙ (B ∙ W ∙ B) ∙ x) ≈⟨⟩
      x ∙ (W ∙ S ∙ L ∙ x)      ≈⟨ ∙-congˡ $ ∙-congʳ $ isWarbler S L ⟩
      x ∙ (S ∙ L ∙ L ∙ x)      ≈⟨ isSageBird ⦃ problem₉ ⦄ x ⟩
      S ∙ L ∙ L ∙ x            ≈˘⟨ ∙-congʳ $ isWarbler S L ⟩
      W ∙ S ∙ L ∙ x            ≈⟨⟩
      W ∙ S ∙ (B ∙ W ∙ B) ∙ x  ∎
  } where instance hasLark = Chapter₁₂.problem₃

problem₁₁ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasMockingbird ⦄ ⦃ _ : HasThrush ⦄ → HasTuringBird
problem₁₁ = record
  { U = B ∙ (B ∙ W ∙ (C ∙ B)) ∙ M
  ; isTuringBird = λ x y → begin
      B ∙ (B ∙ W ∙ (C ∙ B)) ∙ M ∙ x ∙ y  ≈⟨ ∙-congʳ $ isBluebird (B ∙ W ∙ (C ∙ B)) M x ⟩
      B ∙ W ∙ (C ∙ B) ∙ (M ∙ x) ∙ y      ≈⟨ ∙-congʳ $ isBluebird W (C ∙ B) (M ∙ x) ⟩
      W ∙ (C ∙ B ∙ (M ∙ x)) ∙ y          ≈⟨ isWarbler (C ∙ B ∙ (M ∙ x)) y ⟩
      C ∙ B ∙ (M ∙ x) ∙ y ∙ y            ≈⟨ ∙-congʳ $ isCardinal B (M ∙ x) y ⟩
      B ∙ y ∙ (M ∙ x) ∙ y                ≈⟨ isBluebird y (M ∙ x) y ⟩
      y ∙ (M ∙ x ∙ y)                    ≈⟨ ∙-congˡ $ ∙-congʳ $ isMockingbird x ⟩
      y ∙ (x ∙ x ∙ y)                    ∎
  } where
  instance
    hasCardinal = Chapter₁₁.problem₂₁′
    hasLark = Chapter₁₂.problem₇

problem₁₂ : ⦃ _ : HasTuringBird ⦄ → HasSageBird
problem₁₂ = record
  { Θ = U ∙ U
  ; isSageBird = λ x → sym $ isTuringBird U x
  }

problem₁₃ : ⦃ _ : HasQueerBird ⦄ ⦃ _ : HasWarbler ⦄ → HasOwl
problem₁₃ = record
  { O = Q ∙ Q ∙ W
  ; isOwl = λ x y → begin
      Q ∙ Q ∙ W ∙ x ∙ y  ≈⟨ ∙-congʳ $ isQueerBird Q W x ⟩
      W ∙ (Q ∙ x) ∙ y    ≈⟨ isWarbler (Q ∙ x) y ⟩
      Q ∙ x ∙ y ∙ y      ≈⟨ isQueerBird x y y ⟩
      y ∙ (x ∙ y)        ∎
  }

problem₁₄ : ⦃ _ : HasOwl ⦄ ⦃ _ : HasLark ⦄ → HasTuringBird
problem₁₄ = record
  { U = L ∙ O
  ; isTuringBird = λ x y → begin
      L ∙ O ∙ x ∙ y    ≈⟨ ∙-congʳ $ isLark O x ⟩
      O ∙ (x ∙ x) ∙ y  ≈⟨ isOwl (x ∙ x) y ⟩
      y ∙ (x ∙ x ∙ y)  ∎
  }

problem₁₅ : ⦃ _ : HasOwl ⦄ ⦃ _ : HasIdentity ⦄ → HasMockingbird
problem₁₅ = record
  { M = O ∙ I
  ; isMockingbird = λ x → begin
      O ∙ I ∙ x    ≈⟨ isOwl I x ⟩
      x ∙ (I ∙ x)  ≈⟨ ∙-congˡ $ isIdentity x ⟩
      x ∙ x        ∎
  }

problem₁₆ : ⦃ _ : HasStarling ⦄ ⦃ _ : HasIdentity ⦄ → HasOwl
problem₁₆ = record
  { O = S ∙ I
  ; isOwl = λ x y → begin
      S ∙ I ∙ x ∙ y    ≈⟨ isStarling I x y ⟩
      I ∙ y ∙ (x ∙ y)  ≈⟨ ∙-congʳ $ isIdentity y ⟩
      y ∙ (x ∙ y)      ∎
  }

problem₁₇ : ∀ x y → x IsFondOf y → x IsFondOf x ∙ y
problem₁₇ x y xy≈y = begin
  x ∙ (x ∙ y)  ≈⟨ ∙-congˡ xy≈y ⟩
  x ∙ y        ∎

problem₁₈ : ⦃ _ : HasOwl ⦄ ⦃ _ : HasSageBird ⦄ → IsSageBird (O ∙ Θ)
problem₁₈ x = begin
  x ∙ (O ∙ Θ ∙ x)    ≈⟨ ∙-congˡ $ isOwl Θ x ⟩
  x ∙ (x ∙ (Θ ∙ x))  ≈⟨ isFond ⟩
  x ∙ (Θ ∙ x)        ≈˘⟨ isOwl Θ x ⟩
  O ∙ Θ ∙ x          ∎
  where
    isFond : x IsFondOf (x ∙ (Θ ∙ x))
    isFond = problem₁₇ x (Θ ∙ x) (isSageBird x)

problem₁₉ : ⦃ _ : HasOwl ⦄ ⦃ _ : HasSageBird ⦄ → IsSageBird (Θ ∙ O)
problem₁₉ x = sym $ begin
  Θ ∙ O ∙ x        ≈˘⟨ ∙-congʳ $ isSageBird O ⟩
  O ∙ (Θ ∙ O) ∙ x  ≈⟨ isOwl (Θ ∙ O) x ⟩
  x ∙ (Θ ∙ O ∙ x)  ∎

problem₂₀ : ⦃ _ : HasOwl ⦄ → ∀ A → O IsFondOf A → IsSageBird A
problem₂₀ A OA≈A x = begin
  x ∙ (A ∙ x)  ≈˘⟨ isOwl A x ⟩
  O ∙ A ∙ x    ≈⟨ ∙-congʳ OA≈A ⟩
  A ∙ x        ∎

problem₂₁ : ⦃ _ : HasSageBird ⦄ → ∀ A → IsChoosy A → IsSageBird (Θ ∙ A)
problem₂₁ A isChoosy = isChoosy (Θ ∙ A) $ isSageBird A

open import Mockingbird.Forest.Extensionality forest

problem₂₂ : ⦃ _ : HasOwl ⦄ ⦃ _ : HasSageBird ⦄ → O ∙ Θ ≋ Θ
problem₂₂ x = begin
  O ∙ Θ ∙ x    ≈⟨ isOwl Θ x ⟩
  x ∙ (Θ ∙ x)  ≈⟨ isSageBird x ⟩
  Θ ∙ x        ∎

problem₂₃ : ⦃ _ : Extensional ⦄ ⦃ _ : HasOwl ⦄ ⦃ _ : HasSageBird ⦄ → O IsFondOf Θ
problem₂₃ = ext problem₂₂
