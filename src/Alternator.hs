module Alternator where

import Control.Monad

newtype Alternator a = Alternator [a] 
  deriving (Eq, Ord, Show)

toList :: Alternator a -> [a]
toList (Alternator l) = l

fromList :: [a] -> Alternator a
fromList l = Alternator l

instance Applicative Alternator where
  (<*>) = ap
  pure a = Alternator [a]

instance Functor Alternator where
  fmap f (Alternator l) = Alternator (fmap f l)

instance Monad Alternator where
  (Alternator []) >>= _ = Alternator []
  (Alternator (x:xs)) >>= f = 
    case f x of 
      (Alternator []) -> Alternator xs >>= f
      (Alternator (y:ys)) -> Alternator (y:(go ys (toList (Alternator xs >>= f))))
        where
            go :: [a] -> [a] -> [a]
            go l [] = l
            go [] l = l
            go (x:xs) (y:ys) = x:y:(go xs ys)
