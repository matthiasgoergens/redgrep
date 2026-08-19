module Main where
import qualified Data.Set as Set
import qualified Redgrep.Core as C

closureSize :: Int -> C.RE -> Maybe Int
closureSize cap r0 = go (Set.singleton r0) [r0]
  where
    go seen [] = Just (Set.size seen)
    go seen (r : fr)
      | Set.size seen > cap = Nothing
      | otherwise =
          let next = [r' | c <- "ab", let r' = C.deriv c r, not (Set.member r' seen)]
          in go (foldr Set.insert seen next) (next ++ fr)

evil :: Int -> C.RE
evil n = C.seqL (replicate n (C.opt (C.chr 'a')) ++ replicate n (C.chr 'a'))

main :: IO ()
main = mapM_ report [4, 6, 8, 10, 12]
  where
    report n = do
      let states = closureSize 20000 (evil n)
          maxSize = maximum [C.size (C.quotient (replicate k 'a') (evil n)) | k <- [0 .. 2 * n]]
      putStrLn $ "n=" ++ show n
        ++ "  minimal-DFA states (language a^n..a^2n) = " ++ show (2 * n + 2)
        ++ "  our closure = " ++ show states
        ++ "  max term size = " ++ show maxSize
