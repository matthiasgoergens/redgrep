module Util where
import Types
rangeMatch :: Range -> Char -> Maybe Char
rangeMatch Nothing c = Just c
rangeMatch (Just as) c
    | c `elem` as = Just c
    | otherwise = Nothing

