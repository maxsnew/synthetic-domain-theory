{-# OPTIONS --safe --guardedness #-}
module SDT where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Functions.Logic

private
  variable
    ℓ : Level

record Dominance {ℓ} : Type (ℓ-suc ℓ) where
  Ω : Type (ℓ-suc ℓ)
  Ω = hProp ℓ
  field
    _is-semi-decidable : Ω → Ω

  _is-semi-decidable-prop : Type ℓ → Type ℓ
  X is-semi-decidable-prop = Σ[ p ∈ isProp X ] ⟨ (X , p) is-semi-decidable ⟩

  SDProp : hSet (ℓ-suc ℓ)
  SDProp = TypeWithStr ℓ _is-semi-decidable-prop , {!!}

  as-hProp : ⟨ SDProp ⟩ → Ω
  as-hProp X = ⟨ X ⟩ , (fst (snd X))

  hProp→SDProp : (p : Ω) → ⟨ p is-semi-decidable ⟩ → ⟨ SDProp ⟩
  hProp→SDProp p q = ⟨ p ⟩ , ((str p) , q)

  field
    ⊤-is-sd : ⟨ ⊤ is-semi-decidable ⟩
  ⊤' : ⟨ SDProp ⟩
  ⊤' = hProp→SDProp ⊤ ⊤-is-sd

  field
     ∃-is-semi-deciable : (U : ⟨ SDProp ⟩) → (P : ⟨ U ⟩ → ⟨ SDProp ⟩) → ⟨ (∃[ u ] as-hProp (P u)) is-semi-decidable ⟩

  ∃' : (U : ⟨ SDProp ⟩) → (⟨ U ⟩ → ⟨ SDProp ⟩) → ⟨ SDProp ⟩
  ∃' U P = hProp→SDProp (∃[ u ] as-hProp (P u)) (∃-is-semi-deciable U P)

  fst' : ∀ {U P} → ⟨ ∃' U P ⟩ → ⟨ U ⟩
  fst' ex = {!!}

  snd' : ∀ {U P} → (q : ⟨ ∃' U P ⟩) → ⟨ P (fst' {U}{P} q) ⟩
  snd' = {!!}

-- ∃[]-syntax : (A → hProp ℓ) → hProp _
-- ∃[]-syntax {A = A} P = ∥ Σ A (⟨_⟩ ∘ P) ∥ₚ

-- ∃[∶]-syntax : (A → hProp ℓ) → hProp _
-- ∃[∶]-syntax {A = A} P = ∥ Σ A (⟨_⟩ ∘ P) ∥ₚ

-- syntax ∃[∶]-syntax {A = A} (λ x → P) = ∃[ x ∶ A ] P
-- syntax ∃[]-syntax (λ x → P) = ∃[ x ] P
  -- Domains wrt the dominance must live in the next universe in a
  -- predicative theory to accommoddate this notion of lifting.

module LiftMonad (ΣΣ : Dominance {ℓ}) where
  module ΣΣ = Dominance ΣΣ
  open ΣΣ
 -- related: https://arxiv.org/abs/2008.01422
  record L (X : Type (ℓ-suc ℓ)) : Type (ℓ-suc ℓ) where
    inductive
    constructor when_,_
    field
      supp : ⟨ SDProp ⟩
      elt  : ⟨ supp ⟩ → X

  open L
  eqv-toΣ : ∀ {X} → L X ≡ (Σ[ supp ∈ ⟨ SDProp ⟩ ] (⟨ supp ⟩ → X))
  eqv-toΣ = {!isoToEquiv!}

  𝕃 : hSet (ℓ-suc ℓ) → hSet (ℓ-suc ℓ)
  𝕃 X = (L ⟨ X ⟩) , transport (λ i → isSet (sym (eqv-toΣ {⟨ X ⟩}) i)) (isSetΣ {!!} λ x → isSet→ (str X))

  η : ∀ {X} → X → L X
  η x = when ⊤' , (λ _ → x)

  ext : ∀ {X Y} → (X → L Y) → L X → L Y
  ext k l = when ∃' U P ,
                 λ x → L.elt (k (L.elt l (fst' {U}{P} x))) (snd' {U}{P} x)
    where U = L.supp l
          P : ⟨ U ⟩ → ⟨ SDProp ⟩
          P u = L.supp (k (L.elt l u))

  map : ∀ {X Y} → (X → Y) → L X → L Y
  map f = ext λ x → η (f x)

  -- might be useful to have a characterization of equality
  -- l ≡ l' when supp l iff supp l' and (s : supp l) → (s' : supp l') → elt l s ≡ elt l' s'

  L-unit-R : ∀ {X} → (l : L X) → ext {X} η l ≡ l
  L-unit-R = {!!}

  L-unit-L : ∀ {X Y} → (x : X) → (k : X → L Y) → ext k (η x) ≡ k x
  L-unit-L = {!!}

  L-assoc : ∀ {X Y Z} (l : L X) (k : X → L Y) (h : Y → L Z) → ext (λ x → ext h (k x)) l ≡ ext h (ext k l)
  L-assoc = {!!}

  -- L⊥≡⊤ :

  -- initial algebra?
  data ω : Type (ℓ-suc ℓ) where
    think : L ω → ω

  foldω : ∀ {X} → (L X → X) → ω → X
  foldω f (think x) = f (when (L.supp x) , (λ p → foldω f (L.elt x p)))

  -- TODO: prove this is the initial algebra

  -- final algebra
  record ω+ : Type (ℓ-suc ℓ) where
    field
      predicate : ℕ → ⟨ SDProp ⟩
      decreasing   : ∀ n → ⟨ predicate (suc n) ⟩ → ⟨ predicate n ⟩

  -- zero' : ω+
  -- zero' = record { predicate = λ x → ⊥' ; decreasing = λ n z → z }

  limit : ω+
  limit = record { predicate = λ x → ⊤' ; decreasing = λ n _ → tt* }

  open ω+
  suc' : ω+ → ω+
  suc' w = record { predicate = p ; decreasing = d }
    where p : ℕ → ⟨ SDProp ⟩
          p zero = ⊤'
          p (suc n) = predicate w n

          d : ∀ n → ⟨ p (suc n) ⟩ → ⟨ p n ⟩
          d zero = λ _ → tt*
          d (suc n) = decreasing w n

  -- this is the final coalgebra structure described in "A
  -- presentation of the initial lift-algebra" by Mamuka Jibladze
  -- http://www.rmi.ge/~jib/pubs/liftinif.pdf though the result was
  -- also described by Simpson/Rosolini in now possibly lost notes
  pred' : ω+ → L ω+
  pred' w = when (predicate w zero) , (λ _ → record { predicate = λ n → predicate w (suc n) ; decreasing = λ n → decreasing w (suc n) })

  -- TODO: prove this is the final coalgebra
  unfoldω+ : ∀ {X} → (X → L X) → X → ω+
  unfoldω+ {X} g x = record { predicate = {!!} ; decreasing = {!!} }

  -- Should be able to show this is the same as ω+?
  record ω+' : Type (ℓ-suc ℓ) where
    coinductive
    field
      prj : L ω+'

  open ω+'
  unfoldω+' : ∀ {X} → (X → L X) → X → ω+'
  (unfoldω+' g x) .prj = when (L.supp (g x)) , (λ p → unfoldω+' g (L.elt (g x) p))

  ω→ω+ : ω → ω+'
  ω→ω+ = unfoldω+' ω-coalg
    where ω-coalg : ω → L ω
          ω-coalg (think w) = w
          -- equivalently:
          -- ω-coalg = foldω (map think)

  ω-chain : Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
  ω-chain X = ω → X

  limiting-chain : Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
  limiting-chain X = ω+' → X

  has-limit : ∀ {X} → ω-chain X → hProp (ℓ-suc ℓ)
  has-limit {X} chainX = (∃![ limChain ∈ limiting-chain X ] chainX ≡ (λ x → limChain (ω→ω+ x))) , isProp∃!

  is-complete : Type (ℓ-suc ℓ) → hProp (ℓ-suc ℓ)
  is-complete X = (∀ (chain : ω-chain X) → ⟨ has-limit chain ⟩) , isPropΠ λ x → str (has-limit x)

  -- TODO: should almost certainly require them to be hSets as well...
  -- aka "well-complete"
  is-Predomain : Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
  is-Predomain X = ⟨ is-complete (L X) ⟩

  Predomain : Type (ℓ-suc (ℓ-suc ℓ))
  Predomain = TypeWithStr (ℓ-suc ℓ) is-Predomain

module SDT (ΣΣ : Dominance {ℓ})
           (⊥-is-semi-decidable : ⟨ Dominance._is-semi-decidable ΣΣ (⊥* , isProp⊥*) ⟩)
           (Σ-is-complete : ⟨ LiftMonad.is-complete ΣΣ ⟨ Dominance.SDProp ΣΣ ⟩ ⟩)
           where
  -- Do we need another axiom?
  
  -- The last axiom in Fiore-Rosolini is that the lifting functor L
  -- has "rank", meaning it preserves κ-filtered colimits for some
  -- regular cardinal κ.

  -- but they say it is also sufficient that L preserve reflexive
  -- coequalizers which seems maybe possible to prove?

  module ΣΣ = Dominance ΣΣ
  open ΣΣ
  open LiftMonad ΣΣ
  ⊥' : ⟨ SDProp ⟩
  ⊥' = hProp→SDProp (⊥* , isProp⊥*) ⊥-is-semi-decidable

  L0≡1 : L ⊥* ≡ Unit*
  L0≡1 = ua (isoToEquiv (iso (λ x → lift tt) (λ x → LiftMonad.when ⊥' , λ (lift falso) → Cubical.Data.Empty.elim falso) (λ b → refl) λ a → {!!}))
  
