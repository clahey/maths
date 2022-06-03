module clahey.maths.Monoid.Examples where
open import clahey.maths.Monoid using (Monoid)
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

Nat-monoid-+ : Monoid {lzero}
Nat-monoid-+ = record
                 { Underlying = ℕ
                 ; _≈_ = _≡_
                 ; isEquivalence = Relation.Binary.PropositionalEquality.isEquivalence                 
                 ; _∘_ = _+_
                 ; ε = 0
                 ; assoc = λ {a} {b} {c} → +-assoc a b c
                 ; sym-assoc = λ {a} {b} {c} → sym (+-assoc a b c)
                 ; idˡ = +-identityˡ _
                 ; idʳ = +-identityʳ _
                 ; ∘-resp-≈ = ∘-resp-≈
                 }
  where
    ∘-resp-≈ : {a b c d : ℕ} → a ≡ b → c ≡ d → a + c ≡ b + d
    ∘-resp-≈ {a} {.a} {c} {.c} refl refl = refl

Nat-monoid-* : Monoid {lzero}
Nat-monoid-* = record
                 { Underlying = ℕ
                 ; _≈_ = _≡_
                 ; isEquivalence = Relation.Binary.PropositionalEquality.isEquivalence                 
                 ; _∘_ = _*_
                 ; ε = 1
                 ; assoc = λ {a} {b} {c} → *-assoc a b c
                 ; sym-assoc = λ {a} {b} {c} → sym (*-assoc a b c)
                 ; idˡ = *-identityˡ _
                 ; idʳ = *-identityʳ _
                 ; ∘-resp-≈ = ∘-resp-≈
                 }
  where
    ∘-resp-≈ : {a b c d : ℕ} → a ≡ b → c ≡ d → a * c ≡ b * d
    ∘-resp-≈ {a} {.a} {c} {.c} refl refl = refl

List-monoid-++ : {l : Level} → (A : Set l) → Monoid {l} {l}
List-monoid-++ A = record
                     { Underlying = List A
                     ; _≈_ = _≡_
                     ; isEquivalence = Relation.Binary.PropositionalEquality.isEquivalence                 
                     ; _∘_ = _++_
                     ; ε = []
                     ; assoc = λ {f} {g} {h} → assoc {f} {g} {h}
                     ; sym-assoc = λ {f} {g} {h} → sym (assoc {f} {g} {h})
                     ; idˡ = refl
                     ; idʳ = idʳ
                     ; ∘-resp-≈ = ∘-resp-≈
                 }
  where
    assoc : {f g h : List A} → (f ++ g) ++ h ≡ f ++ g ++ h
    assoc {[]} {g} {h} = refl
    assoc {a ∷ f} {g} {h} = cong (a ∷_) (assoc {f} {g} {h})

    idʳ : {f : List A} → f ++ [] ≡ f
    idʳ {[]} = refl
    idʳ {a ∷ f} = cong (a ∷_) (idʳ {f})

    ∘-resp-≈ : {a b c d : List A} → a ≡ b → c ≡ d → a ++ c ≡ b ++ d
    ∘-resp-≈ {a} {.a} {c} {.c} refl refl = refl

List-Pointwise-monoid-++ : {l e : Level} → (A : Set l) → (_≈_ : Rel A e) → IsEquivalence _≈_ → Monoid {l} {l ⊔ e}
List-Pointwise-monoid-++ A _≈_ isEquivalence = record
                     { Underlying = List A
                     ; _≈_ = Pointwise _≈_
                     ; isEquivalence = Data.List.Relation.Binary.Pointwise.isEquivalence isEquivalence
                     ; _∘_ = _++_
                     ; ε = []
                     ; assoc = λ {f} {g} {h} → assoc {f} {g} {h}
                     ; sym-assoc = λ {f} {g} {h} → IsEquivalence.sym (Data.List.Relation.Binary.Pointwise.isEquivalence isEquivalence) (assoc {f} {g} {h})
                     ; idˡ = IsEquivalence.refl ((Data.List.Relation.Binary.Pointwise.isEquivalence isEquivalence))
                     ; idʳ = idʳ
                     ; ∘-resp-≈ = ∘-resp-≈
                     }
  where
    assoc : {f g h : List A} → Pointwise _≈_ ((f ++ g) ++ h) (f ++ g ++ h)
    assoc {[]} {g} {h} = IsEquivalence.refl (Data.List.Relation.Binary.Pointwise.isEquivalence isEquivalence)
    assoc {a ∷ f} {g} {h} = isEquivalence .IsEquivalence.refl Pointwise.∷ assoc {f} {g} {h}

    idʳ : {f : List A} → Pointwise _≈_ (f ++ []) f
    idʳ {[]} = IsEquivalence.refl (Data.List.Relation.Binary.Pointwise.isEquivalence isEquivalence)
    idʳ {a ∷ f} =  isEquivalence .IsEquivalence.refl Pointwise.∷ idʳ {f}

    ∘-resp-≈ : {a b c d : List A} → Pointwise _≈_ a b → Pointwise _≈_ c d → Pointwise _≈_ (a ++ c) (b ++ d)
    ∘-resp-≈ {a} {b} {c} {d} a≈b c≈d = Data.List.Relation.Binary.Pointwise.++⁺ a≈b c≈d
