{-# LANGUAGE DataKinds
           , PolyKinds
           , TypeFamilies
           , TypeOperators
  #-}

module Type.Stack
  (Stack)
where

import Data.Functor.Identity (Identity)

type family Stack fs
  where Stack '[] = Identity
        Stack (f : fs) = f (Stack fs)
