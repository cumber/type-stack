{-# LANGUAGE DataKinds
           , PolyKinds
           , TypeFamilies
           , TypeOperators
  #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Type.Stack
Description : Type level list of transformers as a transformer
Copyright   : © Benjamin Mellor 2016
License     : BSD-style (see the file LICENSE)

Maintainer  : ben@smokingkangaroo.com
Stability   : experimental
Portability : portable

Uses type-level lists to represent a stack of transformers instead of
nesting them. This can lead to type signatures with fewer parentheses,
and cleanly separates the transformer stack from the type it is ultimately
applied to.

This documentation refers to anything of kind @(* -> *) -> (* -> *)@ as a
"transformer". Most usefully these will be monad transfomers, but not all
tools in this library require transformers to be instances of 'MonadTrans'.
-}

module Type.Stack
  (Stack)
where

import Data.Functor.Identity (Identity)

{-|
Stacking a list of transfomers is just their composition applied to
'Identity'.

These types are equivalent:

@
Stack [MaybeT, ReaderT Int]
MaybeT (ReaderT Int Identity)
@
-}
type family Stack fs
  where Stack '[] = Identity
        Stack (f : fs) = f (Stack fs)
