module Mugen.Order.Instances.Singleton where

open import Mugen.Prelude

◆ : ∀ {o r} → Poset o r
◆ .Poset.Ob = Lift _ ⊤
◆ .Poset._≤_ _ _ = Lift _ ⊤
◆ .Poset.≤-thin = hlevel 1
◆ .Poset.≤-refl = lift tt
◆ .Poset.≤-trans p q = p
◆ .Poset.≤-antisym _ _ = refl
