module Main where
import System.Environment
import Parse
import Piless

main = do
  [file] <- getArgs
  e <- parseFile file
  putStr "Term: "
  print e
  case inf e of 
    Right c -> putStr "Type: " >> print (tm c)
    Left err -> putStrLn $ "Type Error: " ++ err


