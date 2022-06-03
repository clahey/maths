module clahey.maths.Group where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
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


record Group {l e : Level } : Set (lsuc (l ⊔ e)) where
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

    _⁻¹ : Underlying → Underlying
    invˡ : {f : Underlying} → f ⁻¹ ∘ f ≈ ε
    invʳ : {f : Underlying} → f ∘ f ⁻¹ ≈ ε
    
record Group-Morphism {l e : Level} (A B : Group {l} {e}) : Set (l ⊔ e) where
  field
    apply : Group.Underlying A → Group.Underlying B
    apply-resp-≈ : { a b : Group.Underlying A } → Group._≈_ A a b → Group._≈_ B (apply a) (apply b)
    apply-resp-∘ : { a b : Group.Underlying A } → Group._≈_ B (Group._∘_ B (apply a) (apply b)) (apply (Group._∘_ A a b))
