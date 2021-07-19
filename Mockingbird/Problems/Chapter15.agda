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
open import Relation.Unary using (Pred)

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

module _ {s} (Sings : Pred Bird s)
         (respects : Sings Respects _≈_) where
  private
    -- TODO: move to Mockingbird.Forest.Axiom(.ExcludedMiddle)?
    ExcludedMiddle : Set (b ⊔ s)
    ExcludedMiddle = ∀ x → Sings x ⊎ ¬ Sings x

    doubleNegation : ExcludedMiddle → ∀ x → ¬ ¬ Sings x → Sings x
    doubleNegation LEM x ¬¬x-sings with LEM x
    ... | inj₁ x-sings = x-sings
    ... | inj₂ ¬x-sings = ⊥-elim $ ¬¬x-sings ¬x-sings

    doubleNegation-⇔ : ExcludedMiddle → ∀ x → (¬ ¬ Sings x) ⇔ Sings x
    doubleNegation-⇔ LEM x = mk⇔ (doubleNegation LEM x) λ x-sings ¬x-sings → ¬x-sings x-sings

    respects-⇔ : ∀ {x y} → x ≈ y → Sings x ⇔ Sings y
    respects-⇔ x≈y = mk⇔ (respects x≈y) (respects (sym x≈y))

  problem₁ :
      ExcludedMiddle
    → ∃[ a ] (∀ x → Sings (a ∙ x) ⇔ Sings (x ∙ x))
    → (∀ x → ∃[ x′ ] (∀ y → Sings (x′ ∙ y) ⇔ (¬ Sings (x ∙ y))))
    → ⊥
  problem₁ LEM (a , is-a) neg =
    let (a′ , is-a′) = neg a

        a′a′-sings⇔¬a′a′-sings : Sings (a′ ∙ a′) ⇔ (¬ Sings (a′ ∙ a′))
        a′a′-sings⇔¬a′a′-sings = ⇔-begin
          Sings (a′ ∙ a′)      ⇔⟨ is-a′ a′ ⟩
          ¬ Sings (a ∙ a′)     ⇔⟨ ⇔-¬ $ is-a a′ ⟩
          (¬ Sings (a′ ∙ a′))  ⇔-∎

        a′a′-sings⇒¬a′a′-sings = Equivalence.f a′a′-sings⇔¬a′a′-sings
        ¬a′a′-sings⇒a′a′-sings = Equivalence.g a′a′-sings⇔¬a′a′-sings

        ↯ : ⊥
        ↯ = case LEM (a′ ∙ a′) of λ
          { (inj₁ a′a′-sings) → a′a′-sings⇒¬a′a′-sings a′a′-sings a′a′-sings
          ; (inj₂ ¬a′a′-sings) → ¬a′a′-sings (¬a′a′-sings⇒a′a′-sings ¬a′a′-sings)
          }
    in ↯

  -- A constructive proof of Russel’s paradox, not using the LEM.
  problem₁′ :
      ∃[ a ] (∀ x → Sings (a ∙ x) ⇔ Sings (x ∙ x))
    → (∀ x → ∃[ x′ ] (∀ y → Sings (x′ ∙ y) ⇔ (¬ Sings (x ∙ y))))
    → ⊥
  problem₁′ (a , is-a) neg =
    let (a′ , is-a′) = neg a

        a′a′-sings⇔¬a′a′-sings : Sings (a′ ∙ a′) ⇔ (¬ Sings (a′ ∙ a′))
        a′a′-sings⇔¬a′a′-sings = ⇔-begin
          Sings (a′ ∙ a′)      ⇔⟨ is-a′ a′ ⟩
          (¬ Sings (a ∙ a′))   ⇔⟨ ⇔-¬ $ is-a a′ ⟩
          (¬ Sings (a′ ∙ a′))  ⇔-∎

    in ⇔-↯ a′a′-sings⇔¬a′a′-sings

  problem₂ : ⦃ _ : HasSageBird ⦄
    → ExcludedMiddle
    → ∃[ N ] (∀ x → Sings x ⇔ (¬ Sings (N ∙ x)))
    → ⊥
  problem₂ LEM (N , is-N) = isNotFond isFond
    where
      isFond : N IsFondOf (Θ ∙ N)
      isFond = isSageBird N

      isNotFond : ¬ N IsFondOf (Θ ∙ N)
      isNotFond isFond with LEM (Θ ∙ N)
      ... | inj₁ ΘN-sings = Equivalence.f (is-N (Θ ∙ N)) ΘN-sings (respects (sym isFond) ΘN-sings)
      ... | inj₂ ¬ΘN-sings =
        let N[ΘN]-sings : Sings (N ∙ (Θ ∙ N))
            N[ΘN]-sings = doubleNegation LEM (N ∙ (Θ ∙ N)) $
              Equivalence.f (⇔-¬ (is-N (Θ ∙ N))) ¬ΘN-sings
        in Equivalence.f (is-N (Θ ∙ N)) (respects isFond N[ΘN]-sings) N[ΘN]-sings

  -- A constructive proof of problem 2, not using the LEM.
  problem₂′ : ⦃ _ : HasSageBird ⦄
    → ∃[ N ] (∀ x → Sings x ⇔ (¬ Sings (N ∙ x)))
    → ⊥
  problem₂′ (N , is-N) = ⇔-↯ ΘN-sings⇔¬ΘN-sings
    where
      isFond : N IsFondOf (Θ ∙ N)
      isFond = isSageBird N

      ΘN-sings⇔¬ΘN-sings : Sings (Θ ∙ N) ⇔ (¬ Sings (Θ ∙ N))
      ΘN-sings⇔¬ΘN-sings = ⇔-begin
        Sings (Θ ∙ N)          ⇔⟨ is-N (Θ ∙ N) ⟩
        ¬ Sings (N ∙ (Θ ∙ N))  ⇔⟨ ⇔-¬ $ respects-⇔ isFond ⟩
        (¬ Sings (Θ ∙ N))      ⇔-∎

  problem₃ : ⦃ _ : HasSageBird ⦄
    → ∃[ A ] (∀ x y → Sings (A ∙ x ∙ y) ⇔ (¬ Sings x × ¬ Sings y))
    → ⊥
  problem₃ (A , is-A) = ↯
    where
      isFond : ∀ {x} → A ∙ x IsFondOf (Θ ∙ (A ∙ x))
      isFond {x} = isSageBird (A ∙ x)

      ¬Θ[Ax]-sings : ∀ x → ¬ Sings (Θ ∙ (A ∙ x))
      ¬Θ[Ax]-sings x Θ[Ax]-sings =
        let Ax[Θ[Ax]]-sings : Sings (A ∙ x ∙ (Θ ∙ (A ∙ x)))
            Ax[Θ[Ax]]-sings = respects (sym isFond) Θ[Ax]-sings

            ¬Θ[Ax]-sings : ¬ Sings (Θ ∙ (A ∙ x))
            ¬Θ[Ax]-sings = proj₂ $ Equivalence.f (is-A x (Θ ∙ (A ∙ x))) Ax[Θ[Ax]]-sings
        in ¬Θ[Ax]-sings Θ[Ax]-sings

      ¬¬x-sings : ∀ x → ¬ ¬ Sings x
      ¬¬x-sings x ¬x-sings =
        let Ax[Θ[Ax]]-sings = Equivalence.g (is-A x (Θ ∙ (A ∙ x))) (¬x-sings , ¬Θ[Ax]-sings x)
            Θ[Ax]-sings = respects isFond Ax[Θ[Ax]]-sings
        in ¬Θ[Ax]-sings x Θ[Ax]-sings

      ↯ : ⊥
      ↯ = ¬¬x-sings (Θ ∙ (A ∙ A)) $ ¬Θ[Ax]-sings A
