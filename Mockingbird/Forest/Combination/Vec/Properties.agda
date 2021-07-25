open import Mockingbird.Forest using (Forest)

module Mockingbird.Forest.Combination.Vec.Properties {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Vec as Vec using (Vec; []; _∷_; _++_)
import Data.Vec.Relation.Unary.Any as Any
open import Data.Vec.Relation.Unary.Any.Properties as Anyₚ using (++⁺ˡ; ++⁺ʳ)
open import Function using (_$_; flip)
open import Relation.Unary using (Pred; _∈_; _⊆_; ∅)

open Forest forest

open import Mockingbird.Forest.Combination.Vec.Base forest
import Mockingbird.Forest.Combination.Properties forest as Combinationₚ

subst : ∀ {n x y} {bs : Vec Bird n} → x ≈ y → x ∈ ⟨ bs ⟩ → y ∈ ⟨ bs ⟩
subst = Combinationₚ.subst λ x≈y → Any.map (trans (sym x≈y))

subst′ : ∀ {n x y} {bs : Vec Bird n} → y ≈ x → x ∈ ⟨ bs ⟩ → y ∈ ⟨ bs ⟩
subst′ y≈x = subst (sym y≈x)

⟨[]⟩ : ⟨ [] ⟩ ⊆ ∅
⟨[]⟩ (X ⟨∙⟩ Y ∣ xy≈z) = ⟨[]⟩ X

weaken-∷ : ∀ {n x y} {bs : Vec Bird n} → x ∈ ⟨ bs ⟩ → x ∈ ⟨ y ∷ bs ⟩
weaken-∷ = Combinationₚ.weaken there

-- TODO: maybe call this ++⁺ˡ.
weaken-++ˡ : ∀ {m n x} {bs : Vec Bird m} {bs′ : Vec Bird n} → x ∈ ⟨ bs ⟩ → x ∈ ⟨ bs ++ bs′ ⟩
weaken-++ˡ {bs = bs} {bs′} [ x∈bs ] = [ ++⁺ˡ x∈bs ]
weaken-++ˡ {bs = bs} {bs′} (x∈⟨bs⟩ ⟨∙⟩ y∈⟨bs⟩ ∣ xy≈z) = weaken-++ˡ x∈⟨bs⟩ ⟨∙⟩ weaken-++ˡ y∈⟨bs⟩ ∣ xy≈z

-- TODO: maybe call this ++⁺ʳ.
weaken-++ʳ : ∀ {m n x} (bs : Vec Bird m) {bs′ : Vec Bird n} → x ∈ ⟨ bs′ ⟩ → x ∈ ⟨ bs ++ bs′ ⟩
weaken-++ʳ bs {bs′} [ x∈bs′ ] = [ ++⁺ʳ bs x∈bs′ ]
weaken-++ʳ bs {bs′} (x∈⟨bs′⟩ ⟨∙⟩ y∈⟨bs′⟩ ∣ xy≈z) = weaken-++ʳ bs x∈⟨bs′⟩ ⟨∙⟩ weaken-++ʳ bs y∈⟨bs′⟩ ∣ xy≈z

++-comm : ∀ {m n x} (bs : Vec Bird m) (bs′ : Vec Bird n) → x ∈ ⟨ bs ++ bs′ ⟩ → x ∈ ⟨ bs′ ++ bs ⟩
++-comm bs bs′ [ x∈bs++bs′ ] = [ Anyₚ.++-comm bs bs′ x∈bs++bs′ ]
++-comm bs bs′ (x∈⟨bs++bs′⟩ ⟨∙⟩ y∈⟨bs++bs′⟩ ∣ xy≈z) = ++-comm bs bs′ x∈⟨bs++bs′⟩ ⟨∙⟩ ++-comm bs bs′ y∈⟨bs++bs′⟩ ∣ xy≈z

open import Mockingbird.Forest.Birds forest
open import Mockingbird.Forest.Extensionality forest
module _ ⦃ _ : Extensional ⦄ ⦃ _ : HasCardinal ⦄ ⦃ _ : HasIdentity ⦄
         ⦃ _ : HasThrush ⦄ ⦃ _ : HasKestrel ⦄ ⦃ _ : HasStarling ⦄ where
  private
    CI≈T : C ∙ I ≈ T
    CI≈T = ext $ λ x → ext $ λ y → begin
      C ∙ I ∙ x ∙ y  ≈⟨ isCardinal I x y ⟩
      I ∙ y ∙ x      ≈⟨ congʳ $ isIdentity y ⟩
      y ∙ x          ≈˘⟨ isThrush x y ⟩
      T ∙ x ∙ y      ∎
  
  _ : T ∈  ⟨ C ∷ I ∷ [] ⟩
  _ = subst CI≈T $ [# 0 ] ⟨∙⟩ [# 1 ]

  _ : I ∈ ⟨ S ∷ K ∷ [] ⟩
  _ = flip subst ([# 0 ] ⟨∙⟩ [# 1 ] ⟨∙⟩ [# 1 ]) $ ext $ λ x → begin
    S ∙ K ∙ K ∙ x    ≈⟨ isStarling K K x ⟩
    K ∙ x ∙ (K ∙ x)  ≈⟨ isKestrel x (K ∙ x) ⟩
    x                ≈˘⟨ isIdentity x ⟩
    I ∙ x            ∎
