module AuxiliaryFunctions where

import Data.List

import DataTypes

isBinderApplied :: Traversal -> String -> Int -> Maybe (UntypedLambda, Int)
isBinderApplied (Tr tr@((_, (_, (_, BIP bip))):_)) z len = let
    tr' = drop (len - bip) tr
  in case tr' of
    (ULAbs _ x _, (_, (CAP cap, _))):_ -> case drop (bip - cap) tr' of
      (ULApp _ _ r, (_, (_, _))):_ -> Just (r, cap)
      _ -> error "isBinderApplied: not an abstraction by BIP from Variable i)"
    -- TODO: м.б. поменять
    (ULAbs _ x _, (_, (LUP lup, _))):_ -> Nothing
    _ -> error "isBinderApplied: not an abstraction by BIP from Variable ii)"
isBinderApplied tr _ _ = error $ "isBinderApplied: not a BIP pointer on input" ++ show tr

isBinderApplied2 :: Traversal -> String -> Int -> Maybe (UntypedLambda, Int)
isBinderApplied2 (Tr tr@((_, (_, (_, BIP bip))):_)) z len = let
    tr' = drop (len - bip) tr
  in case tr' of
    (ULAbs _ x _, (_, (CAP cap, _))):_ -> case drop (bip - cap) tr' of
      (ULApp _ _ r, (_, (_, _))):_ -> Just (r, cap)
      _ -> error "isBinderApplied: not an abstraction by BIP from Variable i)"
    -- TODO: м.б. поменять
    (ULAbs _ x _, (_, (LUP lup, _))):_ -> Nothing
    _ -> error "isBinderApplied: not an abstraction by BIP from Variable ii)"
isBinderApplied2 tr _ _ = Nothing

member x xs = (/=) (filter ((==) x) xs) []