module Parse where
import Text.ParserCombinators.Parsec
import Data.Char (isSpace, isDigit, isLetter)
import Piless

pa <^> pb = pa <* notCode <*> pb 
pa ^> pb  = (pa >> notCode) *> pb
pa <^ pb  = pa <* (notCode >> pb)
infixl 4 <^>, <^, ^>

comment = char '#' >> skipMany (noneOf "\n") >> char '\n'
notCode = ((comment <|> space) >> notCode) <|> return ()

word :: Parser String
word = many1 $ satisfy isLetter

decim :: Parser Int
decim = read <$> many1 digit

parseProgram :: String -> Term 
parseProgram s = parseSource lc s 

parseSource :: Parser Term -> String -> Term
parseSource p src = either (error.show) id . parse p "" $ src

parseFile :: String -> IO Term
parseFile s = parseProgram <$> readFile s

lc :: Parser Term
lc =  Lam <$> ((char '\\' <|> char 'λ') ^> (word <^ char ':')) <^> (lc <^ char '.')  <^> lc
  <|> Pi <$> (char '∀' ^> (word <^ char ':')) <^> (lc <^ char ',')  <^> lc
  <|> Type . toEnum . const 0 <$> (char '*') -- ^> decim)
  <|> Var <$> word
  <|> char '(' ^> (foldl1 App <$> many1 (notCode *> lc <* notCode)) <^ char ')'
  <|> char '[' ^> (foldr1 App <$> many1 (notCode *> lc <* notCode)) <^ char ']'
  <|> char '{' ^> (lets <$> many (notCode *> binding <* notCode) <^> (char '}' ^> lc))
  where lets = flip $ foldr ($) 
        binding = mylet <$> word <^> (char ':' ^> lc) <^> (char '=' ^> lc)
        mylet var ty term body = App (Lam var ty body) term

