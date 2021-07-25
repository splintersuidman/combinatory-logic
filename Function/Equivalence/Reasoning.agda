------------------------------------------------------------------------
-- Reasoning about _⇔_
--
-- NOTE: we don’t use Relation.Binary.IsEquivalence here, since we’re reasoning
-- about a heterogeneous equivalence relation (i.e., the types of the operands
-- of _⇔_, which are themselves types, can be of different levels). In the proof
-- of Chapter₁₅.problem₁, the fact that _⇔_ is heterogeneous is actually used,
-- so we cannot use a homogeneous version of _⇔_.
------------------------------------------------------------------------

module Function.Equivalence.Reasoning where

open import Function using (_⇔_)
open import Function.Construct.Composition using (_∘-⇔_) public
open import Function.Construct.Identity using (id-⇔) public
open import Function.Construct.Symmetry using (sym-⇔) public
open import Level using (Level)

private
  variable
    a b c : Level

infix  1 begin_
infixr 2 _⇔⟨⟩_ step-⇔ step-⇔˘
infix  3 _∎

begin_ : {A : Set a} {B : Set b} → A ⇔ B → A ⇔ B
begin A⇔B = A⇔B

_∎ : (A : Set a) → A ⇔ A
_∎ = id-⇔

_⇔⟨⟩_ : (A : Set a) {B : Set b} → A ⇔ B → A ⇔ B
A ⇔⟨⟩ A⇔B = A⇔B

step-⇔ : (A : Set a) {B : Set b} {C : Set c} → A ⇔ B → B ⇔ C → A ⇔ C
step-⇔ A = _∘-⇔_

syntax step-⇔ A A⇔B B⇔C = A ⇔⟨ A⇔B ⟩ B⇔C

step-⇔˘ : (A : Set a) {B : Set b} {C : Set c} → B ⇔ A → B ⇔ C → A ⇔ C
step-⇔˘ A B⇔A B⇔C = A ⇔⟨ sym-⇔ B⇔A ⟩ B⇔C

syntax step-⇔˘ A B⇔A B⇔C = A ⇔˘⟨ B⇔A ⟩ B⇔C
