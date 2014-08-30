module Background where

postulate Bits : Set

module Open where
  data U : Set where
  
  postulate
    El : U → Set
    marshal : (u : U) → El u → Bits

module Closed where
  data Desc : Set where
  
  postulate
    μ : Desc → Set
    marshal : (D : Desc) → μ D → Bits


