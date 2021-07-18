open import Mockingbird.Forest using (Forest)

-- Russel’s Forest
module Mockingbird.Problems.Chapter15 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; flip; case_of_; _⇔_; Equivalence; mk⇔)
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

⇔-↯ : ∀ {a} {A : Set a} → ¬ (A ⇔ (¬ A))
⇔-↯ {A = A} A⇔¬A = yes but no
  where
    _but_ = flip _$_

    no : ¬ A
    no A = Equivalence.f A⇔¬A A A

    yes : A
    yes = Equivalence.g A⇔¬A no

module _ {d} {Day : Set d} (_SingsOn_ : Bird → Day → Set d)
         (respects : ∀ {d} → (_SingsOn d) Respects _≈_)
         -- Day needs to be inhabited for this proof.
         (day : Day) where
  private
    ExcludedMiddle : Set (b ⊔ d)
    ExcludedMiddle = ∀ x d → (x SingsOn d) ⊎ (¬ x SingsOn d)

    doubleNegation : ExcludedMiddle → ∀ x {d} → ¬ ¬ x SingsOn d → x SingsOn d
    doubleNegation LEM x {d} ¬¬x-sings with LEM x d
    ... | inj₁ x-sings = x-sings
    ... | inj₂ ¬x-sings = ⊥-elim $ ¬¬x-sings ¬x-sings

    doubleNegation-⇔ : ExcludedMiddle → ∀ x {d} → (¬ ¬ x SingsOn d) ⇔ x SingsOn d
    doubleNegation-⇔ LEM x {d} = mk⇔ (doubleNegation LEM x) (λ x-sings ¬x-sings → ¬x-sings x-sings)

    respects-⇔ : ∀ {x y d} → x ≈ y → x SingsOn d ⇔ y SingsOn d
    respects-⇔ x≈y = mk⇔ (respects x≈y) (respects (sym x≈y))

  problem₁ :
      ExcludedMiddle
    → ∃[ a ] (∀ x d → (a ∙ x) SingsOn d ⇔ (x ∙ x) SingsOn d)
    → (∀ x → ∃[ x′ ] (∀ y d → (x′ ∙ y) SingsOn d ⇔ (¬ (x ∙ y) SingsOn d)))
    → ⊥
  problem₁ LEM (a , is-a) neg =
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

    in ⇔-↯ $ a′a′-sings⇔¬a′a′-sings day

  problem₂ : ⦃ _ : HasSageBird ⦄
    → ExcludedMiddle
    → ∃[ N ] (∀ x d → x SingsOn d ⇔ (¬ (N ∙ x) SingsOn d))
    → ⊥
  problem₂ LEM (N , is-N) = isNotFond isFond
    where
      isFond : N IsFondOf (Θ ∙ N)
      isFond = isSageBird N

      isNotFond : ¬ N IsFondOf (Θ ∙ N)
      isNotFond isFond with LEM (Θ ∙ N) day
      ... | inj₁ ΘN-sings = Equivalence.f (is-N (Θ ∙ N) day) ΘN-sings (respects (sym isFond) ΘN-sings)
      ... | inj₂ ¬ΘN-sings =
        let N[ΘN]-sings : (N ∙ (Θ ∙ N)) SingsOn day
            N[ΘN]-sings = doubleNegation LEM (N ∙ (Θ ∙ N)) $
              Equivalence.f (⇔-¬ (is-N (Θ ∙ N) day)) ¬ΘN-sings
        in Equivalence.f (is-N (Θ ∙ N) day) (respects isFond N[ΘN]-sings) N[ΘN]-sings

  -- A constructive proof of problem 2, not using the LEM.
  problem₂′ : ⦃ _ : HasSageBird ⦄
    → ∃[ N ] (∀ x d → x SingsOn d ⇔ (¬ (N ∙ x) SingsOn d))
    → ⊥
  problem₂′ (N , is-N) = ⇔-↯ $ ΘN-sings⇔¬ΘN-sings day
    where
      isFond : N IsFondOf (Θ ∙ N)
      isFond = isSageBird N

      ΘN-sings⇔¬ΘN-sings : ∀ d → (Θ ∙ N) SingsOn d ⇔ (¬ (Θ ∙ N) SingsOn d)
      ΘN-sings⇔¬ΘN-sings d = ⇔-begin
        (Θ ∙ N) SingsOn d          ⇔⟨ is-N (Θ ∙ N) d ⟩
        ¬ (N ∙ (Θ ∙ N)) SingsOn d  ⇔⟨ ⇔-¬ $ respects-⇔ isFond ⟩
        (¬ (Θ ∙ N) SingsOn d)      ⇔-∎

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

      ↯ : ⊥
      ↯ = ¬¬x-sings (Θ ∙ (A ∙ A)) {day} $ ¬Θ[Ax]-sings A
