open import Mockingbird.Forest using (Forest)

module Mockingbird.Forest.Combination.Vec.Base {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≤?_)
open import Data.Vec as Vec using (Vec; _∷_)
open import Data.Vec.Relation.Unary.Any using (here; there) public
open import Level using (_⊔_)
open import Relation.Nullary.Decidable.Core using (True)
open import Relation.Unary using (Pred; _∈_)

open Forest forest

import Mockingbird.Forest.Combination.Base forest as Base
import Mockingbird.Forest.Combination.Properties forest as Combinationₚ
open import Mockingbird.Forest.Combination.Base forest using ([_]; _⟨∙⟩_∣_; _⟨∙⟩_) public
open import Data.Vec.Membership.Setoid setoid using () renaming (_∈_ to _∈′_)

⟨_⟩ : ∀ {n} → Vec Bird n → Pred Bird (b ⊔ ℓ)
⟨ bs ⟩ = Base.⟨ _∈′ bs ⟩

[_]′ : ∀ {n} {bs : Vec Bird n} (i : Fin n) → Vec.lookup bs i ∈ ⟨ bs ⟩
[_]′ {suc n} {x ∷ bs} zero = [ here refl ]
[_]′ {suc n} {x ∷ bs} (suc i) = Combinationₚ.⟨ _ ⟩⊆⟨ _ ⟩ there [ i ]′

[#_] : ∀ m {n} {m<n : True (suc m ≤? n)} {bs : Vec Bird n}
  → Vec.lookup bs (#_ m {m<n = m<n}) ∈ ⟨ bs ⟩
[# m ] = [ # m ]′
