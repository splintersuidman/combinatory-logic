open import Mockingbird.Forest using (Forest)

-- Russel’s Forest
module Mockingbird.Problems.Chapter15 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; case_of_; _⇔_; Equivalence; mk⇔)
open import Function.Equivalence.Reasoning renaming (begin_ to ⇔-begin_; _∎ to _⇔-∎)
open import Level using (_⊔_)
open import Relation.Binary using (_Respects_)
open import Relation.Nullary using (¬_)

open Forest forest
open import Mockingbird.Forest.Birds forest

⇔-¬ : ∀ {a b} {A : Set a} {B : Set b} → A ⇔ B → (¬ A) ⇔ (¬ B)
⇔-¬ A⇔B = record
  { f = λ ¬A b → ¬A (A⇔B.g b)
  ; g = λ ¬B a → ¬B (A⇔B.f a)
  ; cong₁ = λ p → ≡.cong _ p
  ; cong₂ = λ p → ≡.cong _ p
  } where
  module A⇔B = Equivalence A⇔B
  open import Relation.Binary.PropositionalEquality as ≡ using (cong)

module _ {d} {Day : Set d} (_SingsOn_ : Bird → Day → Set d)
         (respects : ∀ {d} → (_SingsOn d) Respects _≈_)
         -- Day needs to be inhabited for this proof.
         (day : Day)
         (LEM : ∀ x d → (x SingsOn d) ⊎ (¬ (x SingsOn d))) where
  private
    doubleNegation : ∀ x {d} → ¬ ¬ x SingsOn d → x SingsOn d
    doubleNegation x {d} ¬¬x-sings with LEM x d
    ... | inj₁ x-sings = x-sings
    ... | inj₂ ¬x-sings = ⊥-elim $ ¬¬x-sings ¬x-sings

    doubleNegation-⇔ : ∀ x {d} → (¬ ¬ x SingsOn d) ⇔ x SingsOn d
    doubleNegation-⇔ x {d} = mk⇔ (doubleNegation x) (λ x-sings ¬x-sings → ¬x-sings x-sings)

  problem₁ :
      ∃[ a ] (∀ x d → (a ∙ x) SingsOn d ⇔ (x ∙ x) SingsOn d)
    → (∀ x → ∃[ x′ ] (∀ y d → (x′ ∙ y) SingsOn d ⇔ (¬ (x ∙ y) SingsOn d)))
    → ⊥
  problem₁ (a , is-a) neg =
    let (a′ , is-a′) = neg a

        a′a′-sings⇔¬a′a′-sings : ∀ d → (a′ ∙ a′) SingsOn d ⇔ (¬ (a′ ∙ a′) SingsOn d)
        a′a′-sings⇔¬a′a′-sings d = ⇔-begin
          (a′ ∙ a′) SingsOn d      ⇔⟨ is-a′ a′ d ⟩
          (¬ (a ∙ a′) SingsOn d)   ⇔⟨ ⇔-¬ (is-a a′ d) ⟩
          (¬ (a′ ∙ a′) SingsOn d)  ⇔-∎

        a′a′-sings⇒¬a′a′-sings = λ d → Equivalence.f (a′a′-sings⇔¬a′a′-sings d)
        ¬a′a′-sings⇒a′a′-sings = λ d → Equivalence.g (a′a′-sings⇔¬a′a′-sings d)

        ↯ : ⊥
        ↯ = case LEM (a′ ∙ a′) day of λ
          { (inj₁ a′a′-sings) → a′a′-sings⇒¬a′a′-sings day a′a′-sings a′a′-sings
          ; (inj₂ ¬a′a′-sings) → ¬a′a′-sings (¬a′a′-sings⇒a′a′-sings day ¬a′a′-sings)
          }
    in ↯

  -- A constructive proof of Russel’s paradox, not using the LEM.
  problem₁′ :
      ∃[ a ] (∀ x d → (a ∙ x) SingsOn d ⇔ (x ∙ x) SingsOn d)
    → (∀ x → ∃[ x′ ] (∀ y d → (x′ ∙ y) SingsOn d ⇔ (¬ (x ∙ y) SingsOn d)))
    → ⊥
  problem₁′ (a , is-a) neg =
    let (a′ , is-a′) = neg a

        a′a′-sings⇔¬a′a′-sings : ∀ d → (a′ ∙ a′) SingsOn d ⇔ (¬ (a′ ∙ a′) SingsOn d)
        a′a′-sings⇔¬a′a′-sings d = ⇔-begin
          (a′ ∙ a′) SingsOn d      ⇔⟨ is-a′ a′ d ⟩
          (¬ (a ∙ a′) SingsOn d)   ⇔⟨ ⇔-¬ (is-a a′ d) ⟩
          (¬ (a′ ∙ a′) SingsOn d)  ⇔-∎

        a′a′-sings⇒¬a′a′-sings = λ {d} → Equivalence.f (a′a′-sings⇔¬a′a′-sings d)
        ¬a′a′-sings⇒a′a′-sings = λ {d} → Equivalence.g (a′a′-sings⇔¬a′a′-sings d)

        ¬¬a′a′-sings : ∀ {d} → ¬ ¬ (a′ ∙ a′) SingsOn d
        ¬¬a′a′-sings ¬a′a′-sings = ¬a′a′-sings (¬a′a′-sings⇒a′a′-sings ¬a′a′-sings)

        ¬a′a′-sings : ∀ {d} → ¬ (a′ ∙ a′) SingsOn d
        ¬a′a′-sings a′a′-sings = a′a′-sings⇒¬a′a′-sings a′a′-sings a′a′-sings

        ↯ : ⊥
        ↯ = ¬¬a′a′-sings {day} ¬a′a′-sings
    in ↯

  problem₂ : ⦃ _ : HasSageBird ⦄
    → ∃[ N ] (∀ x d → x SingsOn d ⇔ (¬ (N ∙ x) SingsOn d))
    → ⊥
  problem₂ (N , is-N) = isNotFond isFond
    where
      isFond : N IsFondOf (Θ ∙ N)
      isFond = isSageBird N

      isNotFond : ¬ N IsFondOf (Θ ∙ N)
      isNotFond isFond with LEM (Θ ∙ N) day
      ... | inj₁ ΘN-sings = Equivalence.f (is-N (Θ ∙ N) day) ΘN-sings (respects (sym isFond) ΘN-sings)
      ... | inj₂ ¬ΘN-sings =
        let N[ΘN]-sings : (N ∙ (Θ ∙ N)) SingsOn day
            N[ΘN]-sings = doubleNegation (N ∙ (Θ ∙ N)) $
              Equivalence.f (⇔-¬ (is-N (Θ ∙ N) day)) ¬ΘN-sings
        in Equivalence.f (is-N (Θ ∙ N) day) (respects isFond N[ΘN]-sings) N[ΘN]-sings

  problem₃ : ⦃ _ : HasSageBird ⦄
    → ∃[ A ] (∀ x y d → (A ∙ x ∙ y) SingsOn d ⇔ (¬ x SingsOn d × ¬ y SingsOn d))
    → ⊥
  problem₃ (A , is-A) = ↯
    where
      isFond : ∀ {x} → A ∙ x IsFondOf (Θ ∙ (A ∙ x))
      isFond {x} = isSageBird (A ∙ x)

      ¬Θ[Ax]-sings : ∀ x {d} → ¬ (Θ ∙ (A ∙ x)) SingsOn d
      ¬Θ[Ax]-sings x {d} Θ[Ax]-sings =
        let Ax[Θ[Ax]]-sings : (A ∙ x ∙ (Θ ∙ (A ∙ x))) SingsOn d
            Ax[Θ[Ax]]-sings = respects (sym isFond) Θ[Ax]-sings

            ¬Θ[Ax]-sings : ¬ (Θ ∙ (A ∙ x)) SingsOn d
            ¬Θ[Ax]-sings = proj₂ $ Equivalence.f (is-A x (Θ ∙ (A ∙ x)) d) Ax[Θ[Ax]]-sings
        in ¬Θ[Ax]-sings Θ[Ax]-sings

      ¬¬x-sings : ∀ x {d} → ¬ ¬ x SingsOn d
      ¬¬x-sings x {d} ¬x-sings =
        let Ax[Θ[Ax]]-sings = Equivalence.g (is-A x (Θ ∙ (A ∙ x)) d) (¬x-sings , ¬Θ[Ax]-sings x)
            Θ[Ax]-sings = respects isFond Ax[Θ[Ax]]-sings
        in ¬Θ[Ax]-sings x Θ[Ax]-sings

      x-sings : ∀ x {d} → x SingsOn d
      x-sings x = doubleNegation x $ ¬¬x-sings x

      ↯ : ⊥
      ↯ = ¬Θ[Ax]-sings A {day} $ x-sings $ Θ ∙ (A ∙ A)
