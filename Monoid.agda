module clahey.maths.Monoid where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤?_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; +-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Level using (Lift; lift)
open import Agda.Primitive using (Level; lsuc; _⊔_; lzero)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using (List; _++_; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary using (Rel; IsPreorder; IsDecEquivalence; IsEquivalence)
open import Relation.Binary.Definitions using (Decidable)
open import Data.Bool using (true; false)


record Monoid {l e : Level} : Set (lsuc (l ⊔ e)) where
  infix  4 _≈_
  infixr 9 _∘_
  field
    Underlying : Set l
    _≈_ : Rel Underlying e
    isEquivalence : IsEquivalence _≈_
    _∘_ : Underlying → Underlying → Underlying
    ε : Underlying
    assoc : {f g h : Underlying} → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
    sym-assoc : {f g h : Underlying} → f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
    idˡ : {f : Underlying} → ε ∘ f ≈ f
    idʳ : {f : Underlying} → f ∘ ε ≈ f
    ∘-resp-≈ : {f g h i : Underlying} → f ≈ g → h ≈ i → f ∘ h ≈ g ∘ i
