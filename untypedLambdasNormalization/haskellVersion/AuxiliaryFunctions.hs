module AuxiliaryFunctions (isBinderApplied, isBinderApplied2, member) where

import Data.List

import DataTypes

isBinderApplied  :: Traversal -> String -> Int -> Maybe (UntypedLambda, Int)
isBinderApplied  t z len = isBinderApplied0 t z len (error "isBinderApplied2: not an abstraction by BIP from Variable ii)")
isBinderApplied2 :: Traversal -> String -> Int -> Maybe (UntypedLambda, Int)
isBinderApplied2 t z len = isBinderApplied0 t z len Nothing

isBinderApplied0 :: Traversal -> String -> Int -> Maybe (UntypedLambda, Int) -> Maybe (UntypedLambda, Int)
isBinderApplied0 (Tr tr@((_, (_, (_, BIP bip))):_)) z len f = let
    tr' = drop (len - bip) tr
  in case tr' of
    (ULAbs _ x _, (_, (CAP cap, _))):_ -> case drop (bip - cap) tr' of
      (ULApp _ _ r, (_, (_, _))):_ -> Just (r, cap)
      _ -> error "isBinderApplied: not an abstraction by BIP from Variable i)"
    -- TODO: м.б. поменять
    (ULAbs _ x _, (_, (LUP   lup, _))):_ -> Nothing
    (ULAbs _ x _, (_, (PAUSE lup, _))):_ -> Nothing
    _ -> error "isBinderApplied: not an abstraction by BIP from Variable ii)"
isBinderApplied0 tr _ _ f = f

member x xs = (/=) (filter ((==) x) xs) []