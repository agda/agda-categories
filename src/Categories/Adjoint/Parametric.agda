module Categories.Adjoint.Parametric where

open import Level

open import Data.Product using (_×_; _,_)
open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open Categories.Functor.Functor using (F₀; F₁; homomorphism; identity; F-resp-≈)
open import Categories.Adjoint using (Adjoint)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Diagram.Cowedge using (Cowedge)
open import Categories.NaturalTransformation.Dinatural using (dtHelper)
open import Categories.Functor.Bifunctor using (Bifunctor)
import Categories.NaturalTransformation
open Categories.NaturalTransformation.NaturalTransformation using (η; commute)
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

-- A parametric adjunction is a family of functors Lc ⊣ Rc indexed by an object c of
-- a category C; equivalently, a pair of functors L : C x D → E and R : Cᵒ x E → D
-- such that for every c in C Lc = L(c,-) ⊣ R(c,-) = Rc.
record ParametricAdjoint {C D E : Category o ℓ e} (L : Functor C (Functors D E)) (R : Functor (Category.op C) (Functors E D)) : Set (o ⊔ ℓ ⊔ e) where
  private
    module C = Category C
    module D = Category D
    module E = Category E
    module L = Functor L
    module R = Functor R
    -- use double letters whenever we refer to the two-parameters version of the functor
    module RR A = Functor (R.₀ A)
    module LL A = Functor (L.₀ A)
  field
    areAdjoint : ∀ A → Adjoint (L.₀ A) (R.₀ A)

  module A c = Adjoint (areAdjoint c)

  {-
    We seem to need a field ensuring that the adjunction L c ⊣ R c is natural in (c : C),
    which means that the square

      hom(L(c , x) , y) ----------------→ hom(x , R(c , y))
        ↑                                          ↑
        |                                          |
        |                                          |
        |                                          |
      hom(L(c' , x) , y) ---------------→ hom(x , R(c' , y))

    is commutative; unfolding the definitions, it seems that proving this exactly amounts to show
    that the *unit* η c of the adjunction is a *wedge*. Viceversa, one also needs this naturality
    when proving that the cowedge condition holds, so they seem to be logically equivalent.
    Mac Lane (IV.7.Thm 3) seems to claim, however, that this condition needs not to be assumed
    and can be derived from a better definition of parametric adjunction that we are not
    currently able to devise.

    More info at: https://math.stackexchange.com/questions/4581092/parametric-adjunctions-induce-cowedges-a-real-proof
  -}

  field
    param-nat : ∀ {c c' x y} {f : c C.⇒ c'} {u : LL.₀ c' x E.⇒ y} →
      RR.₁ c u D.∘ RR.₁ c (η (L.₁ f) x) D.∘ η (A.unit c) x D.≈
      η (R.₁ f) y D.∘ RR.₁ c' u D.∘ η (A.unit c') x

  -- Every parametric adjunction Lc ⊣ Rc defines a bifunctor L(-,R(-,x)) : Cᵒ x C → E
  PABifunctor : {X : E.Obj} → Bifunctor C.op C E
  PABifunctor {X} = record
    { F₀ = λ { (c , c') → LL.₀ c' (RR.₀ c X)}
    ; F₁ = λ { {a , a'} {b , b'} (f , f') →
        η (L.₁ f') (RR.₀ b X) E.∘ LL.₁ a' (η (R.₁ f) X)}
    ; identity = λ { {a , a'} →
        begin _ ≈⟨ L.identity ⟩∘⟨ Functor.F-resp-≈ (L.₀ a') R.identity ⟩
              _ ≈⟨ refl⟩∘⟨ Functor.identity (L.₀ a') ⟩
              _ ≈⟨ E.identity² ⟩
              _ ∎ }
    ; homomorphism = λ { {a , a'} {b , b'} →
        begin _ ≈⟨ pushˡ L.homomorphism ⟩
              _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.F-resp-≈ (L.₀ a') R.homomorphism ⟩
              _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.homomorphism (L.₀ a') ⟩
              _ ≈⟨ refl⟩∘⟨ pullˡ (commute (L.₁ _) _) ⟩
              _ ≈⟨ MR.assoc²'' E ⟩
              _ ∎ }
    ; F-resp-≈ = λ { {a , a'} {b , b'} {f} {g} (f≈g , f'≈g') →
        L.F-resp-≈ f'≈g' ⟩∘⟨ Functor.F-resp-≈ (L.₀ a') (R.F-resp-≈ f≈g)}
    } where
        open E.HomReasoning
        open MR E

  -- this is the main theorem of the module: a parametric adjunction Lc ⊣ Rc has a
  -- counit ε[c,x] : L(c,R(c,x)) → x; this map is a cowedge in c.
  counitCowedge : ∀ {A : Category.Obj E} → Cowedge {C = C} {D = E} (PABifunctor {A})
  counitCowedge {A} = record
    { E = A
    ; dinatural = dtHelper record
      { α = λ c → A.counit.η c _
      ; commute = λ {X} {Y} f →
        let
          open Adjoint

          adjunction-isoˡ : A.Ladjunct X (A.counit.η X A E.∘ LL.₁ X (η (R.₁ f) A)) D.≈
                            η (R.₁ f) A
          adjunction-isoˡ = let open D.HomReasoning; open MR D in
            begin _ ≈⟨ pushˡ (homomorphism (R.₀ X)) ⟩
                  _ ≈⟨ pushʳ (D.Equiv.sym (A.unit.commute X _)) ⟩
                  _ ≈⟨ A.zag X ⟩∘⟨refl ⟩
                  _ ≈⟨ D.identityˡ ⟩
                  _ ∎

          adjunction-isoʳ : A.Ladjunct X (A.counit.η Y A E.∘ η (L.₁ f) (RR.₀ Y A)) D.≈
                            η (R.₁ f) A
          adjunction-isoʳ = let open D.HomReasoning; open MR D in
            begin _ ≈⟨ pushˡ (homomorphism (R.₀ X)) ⟩
                  _ ≈⟨ param-nat ⟩
                  _ ≈⟨ refl⟩∘⟨ zag (areAdjoint Y) ⟩
                  _ ≈⟨ refl⟩∘⟨ D.Equiv.sym (identity (R.₀ Y)) ⟩
                  _ ≈⟨ refl⟩∘⟨ identity (R.₀ Y) ⟩
                  _ ≈⟨ D.identityʳ ⟩
                  _ ∎

          adjunction-iso : A.Ladjunct X (A.Radjunct X (η (R.₁ f) A))
                       D.≈ A.Ladjunct X (A.counit.η Y A E.∘ η (L.₁ f) (RR.₀ Y A))
          adjunction-iso = D.Equiv.trans adjunction-isoˡ (D.Equiv.sym adjunction-isoʳ)

          is-cowedge : A.Radjunct X (η (R.₁ f) A)
                   E.≈ A.counit.η Y A E.∘ η (L.₁ f) (RR.₀ Y A)
          is-cowedge = Adjoint.Hom-inverse.injective (areAdjoint X) adjunction-iso

          -- in the proof the meat is in `is-cowedge`; but due to the definition of
          -- cowedge using the constant bifunctor, Agda wants the proof term wrapped
          -- in some identities.
       in let open E.HomReasoning; open MR E in begin
            _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimˡ L.identity ⟩
            _ ≈⟨ refl⟩∘⟨ is-cowedge ⟩
            _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ introʳ (identity (L.₀ _)) ⟩
            _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ F-resp-≈ (L.₀ _) (D.Equiv.sym R.identity) ⟩
            _ ∎
      }
    }
