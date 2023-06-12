module Main where

import System.IO
import Prover (prover)
import Parser hiding (one)

main :: IO ()
main = do
    eof <- isEOF
    if eof
        then return ()
        else do
          line <- getLine -- read the input
          let phi = parseString line -- call the parser
          let res = prover phi -- call the prover
          if res
            then putStrLn "1" -- write 1 if the formula is a tautology
            else putStrLn "0" -- write 0 if the formula is not a tautology
