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
           , ConstraintKinds
           , DataKinds
           , FlexibleContexts
           , FlexibleInstances
           , InstanceSigs
           , MagicHash
           , MultiParamTypeClasses
           , PolyKinds
           , RankNTypes
           , ScopedTypeVariables
           , TypeApplications
           , TypeFamilyDependencies
           , TypeOperators
           , UndecidableInstances
           , UndecidableSuperClasses
  #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module Type.Stack
  ( Stack
  , type (@@)
  , liftStack
  )
where

import Control.Monad.Trans.Class

import qualified Data.Constraint as Constraint
import Data.Constraint ((:-))
import qualified Data.Constraint.Lifting as Constraint

import Data.Functor.Identity (Identity)

import Data.Kind (Constraint)


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


newtype ApplyConcat fs t
  = ApplyConcat { getApplied :: Stack' fs t }


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

type family xs <> ys
  where '[] <> ys = ys
        (x : xs) <> ys = x : (xs <> ys)

class (All (Constraint.Lifting Monad) fs, LiftingThroughStack fs) => LiftStack fs
  where liftStack :: Monad m => m a -> Stack' fs m a

instance LiftStack '[]
  where liftStack = id

instance (LiftStack fs, MonadTrans f, Constraint.Lifting Monad f) => LiftStack (f : fs)
  where liftStack :: forall m a. Monad m => m a -> (Stack' (f : fs) m) a
        liftStack
          = case Constraint.lifting @ Monad @ f @ m of
              Constraint.Sub Constraint.Dict
                ->  case liftingThroughStack @ fs @ Monad @ m of
                      Constraint.Sub Constraint.Dict
                        ->  lift . liftStack @ fs

type family All constraint (ts :: [(* -> *) -> (* -> *)]) = (r :: Constraint) | r -> ts
  where All c '[] = ()
        All c (t : ts) = (c t, All c ts)

{-
class LiftingThroughStack fs
  where liftingThroughStack
         :: c m
         => All (Constraint.Lifting c) fs :- c (Stack' fs m)

instance LiftingThroughStack '[]
  where liftingThroughStack = Constraint.Sub Constraint.Dict

instance LiftingThroughStack fs => LiftingThroughStack (f : fs)
  where liftingThroughStack
         :: forall c m
          . c m
         => All (Constraint.Lifting c) (f : fs) :- c (Stack' (f : fs) m)

        liftingThroughStack
          = Constraint.Sub
              ( case liftingThroughStack @ fs @ c @ m of
                  Constraint.Sub Constraint.Dict
                    ->  case Constraint.lifting @ c @ f @ (Stack' fs m) of
                          Constraint.Sub Constraint.Dict -> Constraint.Dict
              )
-}

class LiftingThroughStack fs
  where liftingThroughStack :: c t => All (Constraint.Lifting c) fs :- c (ApplyConcat fs)


{-
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
-}
