-- Kapitel 1, Abschnitt D (Die Eigenschaften der Gleichheit)
module CombinatoryLogic.Equality where

open import Algebra.Definitions using (Congruent₂; LeftCongruent; RightCongruent)
open import Data.Vec using (Vec; []; _∷_; foldr₁; lookup)
open import Function using (_$_)
open import Relation.Binary using (IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CombinatoryLogic.Semantics
open import CombinatoryLogic.Syntax

private
  -- A lemma used in the proofs of Propositions 1 and 2.
  lemma-CQXX : ∀ {X} → ⊢ C ∙ Q ∙ X ∙ X
  lemma-CQXX {X} =
    let s₁ = ⊢ Π ∙ (W ∙ (C ∙ Q))                        [ ax Q ]
        s₂ = ⊢ W ∙ (C ∙ Q) ∙ X                          [ Π s₁ ]
        s₃ = ⊢ Q ∙ (W ∙ (C ∙ Q) ∙ X) ∙ (C ∙ Q ∙ X ∙ X)  [ W ]
        s₄ = ⊢ C ∙ Q ∙ X ∙ X                            [ Q₁ s₂ s₃ ]
    in s₄

-- Satz 1
prop₁ : ∀ {X} → ⊢ Q ∙ X ∙ X
prop₁ {X} = s₆ where
  s₄ = ⊢ C ∙ Q ∙ X ∙ X                            [ lemma-CQXX ]
  s₅ = ⊢ Q ∙ (C ∙ Q ∙ X ∙ X) ∙ (Q ∙ X ∙ X)        [ C ]
  s₆ = ⊢ Q ∙ X ∙ X                                [ Q₁ s₄ s₅ ]

-- Satz 2
prop₂ : ∀ {X Y} → ⊢ Q ∙ X ∙ Y → ⊢ Q ∙ Y ∙ X
prop₂ {X} {Y} ⊢QXY = s₅ where
  s₁ = ⊢ Q ∙ X ∙ Y                             [ ⊢QXY ]
  -- NOTE: Curry's proof contains a mistake: CQXX should be CQXY.
  s₂ = ⊢ Q ∙ (C ∙ Q ∙ X ∙ X) ∙ (C ∙ Q ∙ X ∙ Y) [ Q₂ {Z = C ∙ Q ∙ X} s₁ ]
  s₃ = ⊢ C ∙ Q ∙ X ∙ X                         [ lemma-CQXX ]
  -- NOTE: Curry's proof uses rule Q, but there is no such rule.
  s₄ = ⊢ C ∙ Q ∙ X ∙ Y                         [ Q₁ s₃ s₂ ]
  s₅ = ⊢ Q ∙ Y ∙ X                             [ Q₁ s₄ C ]

-- Satz 3
prop₃ : ∀ {X Y Z} → ⊢ Q ∙ X ∙ Y → ⊢ Q ∙ Y ∙ Z → ⊢ Q ∙ X ∙ Z
prop₃ {X} {Y} {Z} ⊢QXY ⊢QYZ = s₃ where
  s₁ = ⊢ Q ∙ Y ∙ Z                     [ ⊢QYZ ]
  s₂ = ⊢ Q ∙ (Q ∙ X ∙ Y) ∙ (Q ∙ X ∙ Z) [ Q₂ {Z = Q ∙ X} s₁ ]
  s₃ = ⊢ Q ∙ X ∙ Z                     [ Q₁ ⊢QXY s₂ ]

-- Satz 4
prop₄ : ∀ {X Y Z} → ⊢ Q ∙ X ∙ Y → ⊢ Q ∙ (X ∙ Z) ∙ (Y ∙ Z)
prop₄ {X} {Y} {Z} Hp = s₅ where
  p₁ = λ {X} → ⊢ Q ∙ (C ∙ (B ∙ (W ∙ K)) ∙ Z ∙ X) ∙ (B ∙ (W ∙ K) ∙ X ∙ Z)  [ C ]
  p₂ = λ {X} → ⊢ Q ∙ (B ∙ (W ∙ K) ∙ X ∙ Z) ∙ (W ∙ K ∙ (X ∙ Z))            [ B ]
  p₃ = λ {X} → ⊢ Q ∙ (W ∙ K ∙ (X ∙ Z)) ∙ (K ∙ (X ∙ Z) ∙ (X ∙ Z))          [ W ]
  p₄ = λ {X} → ⊢ Q ∙ (K ∙ (X ∙ Z) ∙ (X ∙ Z)) ∙ (X ∙ Z)                    [ K ]
  p₅ = λ {X} → ⊢ Q ∙ (C ∙ (B ∙ (W ∙ K)) ∙ Z ∙ X) ∙ (X ∙ Z)                [ prop₃ p₁ $ prop₃ p₂ $ prop₃ p₃ p₄ ]
  s₁ = ⊢ Q ∙ (C ∙ (B ∙ (W ∙ K)) ∙ Z ∙ X) ∙ (C ∙ (B ∙ (W ∙ K)) ∙ Z ∙ Y)  [ Q₂ Hp ]
  s₂ = ⊢ Q ∙ (C ∙ (B ∙ (W ∙ K)) ∙ Z ∙ X) ∙ (X ∙ Z)                      [ p₅ ]
  s₃ = ⊢ Q ∙ (C ∙ (B ∙ (W ∙ K)) ∙ Z ∙ Y) ∙ (Y ∙ Z)                      [ p₅ ]
  s₄ = ⊢ Q ∙ (X ∙ Z) ∙ (C ∙ (B ∙ (W ∙ K)) ∙ Z ∙ X)                      [ prop₂ s₂ ]
  s₅ = ⊢ Q ∙ (X ∙ Z) ∙ (Y ∙ Z)                                          [ prop₃ s₄ $ prop₃ s₁ s₃ ]

-- Satz 5
prop₅ : ∀ {X Y} → X ≡ Y → ⊢ Q ∙ X ∙ Y
prop₅ {X} {Y} refl = prop₁

-- Satz 6 (first part)
isEquivalence : IsEquivalence _≈_
isEquivalence = record
  { refl = prop₁
  ; sym = prop₂
  ; trans = prop₃
  }

setoid : Setoid _ _
setoid = record
  { Carrier = Combinator
  ; _≈_ = _≈_
  ; isEquivalence = isEquivalence
  }

module Reasoning where
  module ≈ = IsEquivalence isEquivalence
  import Relation.Binary.Reasoning.Base.Single _≈_ ≈.refl ≈.trans as Base
  open Base using (begin_; _∎) public

  infixr 2 _≈⟨⟩_ step-≈ step-≈˘

  _≈⟨⟩_ : ∀ x {y} → x Base.IsRelatedTo y → x Base.IsRelatedTo y
  _ ≈⟨⟩ x≈y = x≈y

  step-≈ = Base.step-∼
  syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

  step-≈˘ : ∀ x {y z} → y Base.IsRelatedTo z → y ≈ x → x Base.IsRelatedTo z
  step-≈˘ x y∼z y≈x = x ≈⟨ ≈.sym y≈x ⟩ y∼z
  syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z

-- Satz 6 (second part)
∙-cong : Congruent₂ _≈_ _∙_
∙-cong {X} {X′} {Y} {Y′} ⊢X==X′ ⊢Y==Y′ = s₃ where
  s₁ = ⊢ X ∙ Y == X ∙ Y′    [ Q₂ ⊢Y==Y′ ]
  s₂ = ⊢ X ∙ Y′ == X′ ∙ Y′  [ prop₄ ⊢X==X′ ]
  s₃ = ⊢ X ∙ Y == X′ ∙ Y′   [ prop₃ s₁ s₂ ]

-- ∙-congˡ and ∙-congʳ follow from ∙-cong, but are also just different names for
-- Q₂ and prop₄, respectively.
∙-congˡ : LeftCongruent _≈_ _∙_
∙-congˡ = Q₂

∙-congʳ : RightCongruent _≈_ _∙_
∙-congʳ = prop₄

-- TODO: Satz 7, 8

prop₉ : ∀ {X} → ⊢ I ∙ X == X
prop₉ {X} = begin
  I ∙ X      ≈⟨⟩
  W ∙ K ∙ X  ≈⟨ W ⟩
  K ∙ X ∙ X  ≈⟨ K ⟩
  X          ∎
  where open Reasoning

-- Note after the proof of Satz 9.
S : Combinator
S = B ∙ (B ∙ W) ∙ (B ∙ B ∙ C)

prop-S : ∀ {X} {Y} {Z} → ⊢ S ∙ X ∙ Y ∙ Z == X ∙ Z ∙ (Y ∙ Z)
prop-S {X} {Y} {Z} = begin
  S ∙ X ∙ Y ∙ Z                          ≈⟨⟩
  B ∙ (B ∙ W) ∙ (B ∙ B ∙ C) ∙ X ∙ Y ∙ Z  ≈⟨ ∙-congʳ $ ∙-congʳ B ⟩
  B ∙ W ∙ (B ∙ B ∙ C ∙ X) ∙ Y ∙ Z        ≈⟨ ∙-congʳ B ⟩
  W ∙ (B ∙ B ∙ C ∙ X ∙ Y) ∙ Z            ≈⟨ W ⟩
  B ∙ B ∙ C ∙ X ∙ Y ∙ Z ∙ Z              ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ B ⟩
  B ∙ (C ∙ X) ∙ Y ∙ Z ∙ Z                ≈⟨ ∙-congʳ B ⟩
  C ∙ X ∙ (Y ∙ Z) ∙ Z                    ≈⟨ C ⟩
  X ∙ Z ∙ (Y ∙ Z)                        ∎
  where open Reasoning

-- TODO: ⊢ B == S(KS)K, ⊢ C == S(BBS)(KK), ⊢ W == SS(SK), ⊢ I == SKK
