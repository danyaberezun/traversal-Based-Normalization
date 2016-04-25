module AuxiliaryFunctions (isBinderApplied, isBinderApplied2, member) where

import           DataTypes

isBinderApplied  :: Traversal -> String -> Int -> Maybe (UntypedLambda, Int)
isBinderApplied  t z len =
  isBinderApplied0 t z len
  (error "isBinderApplied2: not an abstraction by BIP from Variable ii)")
isBinderApplied2 :: Traversal -> String -> Int -> Maybe (UntypedLambda, Int)
isBinderApplied2 t z len = isBinderApplied0 t z len Nothing

isBinderApplied0 :: Traversal -> String -> Int -> Maybe (UntypedLambda, Int)
                    -> Maybe (UntypedLambda, Int)
isBinderApplied0 (Tr tr@((_, (_, (_, BIP bip))):_)) _ len _ = let
    tr' = drop (len - bip) tr
  in case tr' of
    (ULAbs {}, (_, (CAP cap, _))):_ -> case drop (bip - cap) tr' of
      (ULApp _ _ r, (_, (_, _))):_ -> Just (r, cap)
      _ -> error "isBinderApplied: not an abstraction by BIP from Variable i)"
    -- TODO: м.б. поменять
    (ULAbs {}, (_, (LUP   _, _))):_ -> Nothing
    (ULAbs {}, (_, (PAUSE _, _))):_ -> Nothing
    _ -> error "isBinderApplied: not an abstraction by BIP from Variable ii)"
isBinderApplied0 _ _ _ f = f

member :: Eq a => a -> [a] -> Bool
member x xs = (/=) (filter (x ==) xs) []
