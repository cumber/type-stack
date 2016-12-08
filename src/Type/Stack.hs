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

{-# LANGUAGE AllowAmbiguousTypes
           , DataKinds
           , FlexibleContexts
           , FlexibleInstances
           , MagicHash
           , MultiParamTypeClasses
           , PolyKinds
           , ScopedTypeVariables
           , TypeApplications
           , TypeFamilyDependencies
           , TypeOperators
  #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module Type.Stack
  ( Stack
  , type (@@)
  , liftStack
  )
where

import Control.Monad.Trans.Class

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
type family Stack fs = r | r -> fs
  where Stack '[] = Identity
        Stack (f : fs) = f (Stack fs)


type family Stack' fs m = r
  where Stack' '[] m = m
        Stack' (f : fs) m = f (Stack' fs m)

{-|
An infix operator for 'Stack'ing a list of transformers and applying
the result to a type.

These types are equivalent:

@
[ReaderT Int, MaybeT] @@ Bool
Stack [ReaderT Int, MaybeT] Bool
ReaderT Int (MaybeT Identity) Bool
@
-}
type fs @@ a = Stack fs a


type family Prefix fs gs
  where Prefix fs fs = '[]
        Prefix (f : fs) gs = f ': Prefix fs gs


liftStack
 :: forall inner full prefix a
  . ( prefix ~ Prefix full inner
    , Stack' prefix (Stack inner) ~ Stack full
    , LiftStack prefix (Stack inner)
    )
 => inner @@ a -> full @@ a
liftStack = liftStack' @ prefix


class Monad (Stack' fs base) => LiftStack fs base
  where liftStack' :: base a -> Stack' fs base a

instance Monad m => LiftStack '[] m
  where liftStack' = id

instance (LiftStack fs m, Monad (f (Stack' fs m)), MonadTrans f) => LiftStack (f : fs) m
  where liftStack' = lift . liftStack' @ fs
