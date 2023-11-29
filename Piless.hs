module Piless where
import Nat
import qualified DB
import Debug.Trace

data Term = Var String 
          | Lam Bool String Term Term
          | Type N 
          | App Term Term

-- Equality is equality of deBruijn terms
instance Eq Term where
  a == b = db a == db b

-- Turns a closed term into deBruijn notation, returns unbound variable name in
-- failure
db :: Term -> Either String DB.Term 
db t = f t []  where  
  f :: Term -> [(String, Int)] -> Either String DB.Term 
  f t e = case t of
    Var v -> maybe (Left $ "unbound var: " ++  v) (Right . DB.Var) $ lookup v e
    Lam pi v tau b -> DB.Lam pi <$> f tau e <*> f b ((v, 0):map (fmap succ) e)
    Type n -> pure $ DB.Type n
    App m n -> DB.App <$> f m e <*> f n e

instance Show Term where
  show (App (Lam False v tau b) e) = "let " ++ v ++ " : " ++ show tau ++ " = " ++ show e ++ " in \n" ++ show b 
  show (Lam pi v tau b) = (if pi then "∀" else "λ") ++ v ++ ":" ++ show tau ++ "." ++ show b 
  show (App m n) = "(" ++ show m ++ " " ++ show n ++ ")"
  show (Type n) = "*"
  show (Var v) = v

subst :: String -> Term -> Term -> Term
subst x t e = case e of
  Var v | x == v -> t
  Lam pi v t' b -> Lam pi v (subst x t t') $ if x /= v then subst x t b else b
  App m n -> App (subst x t m) (subst x t n)
  _ -> e

eval :: Closure -> Closure
eval c@(Close t ctx) = case t of
  Var v -> case lookup v ctx of
    Nothing -> error ("unbound variable lookup " ++ show v) --error $ "Unbound variable in evaluation: " ++ v 
    Just (Just c, _) -> eval c
    Just (Nothing, _) -> {-trace ("context only type for " ++ v)-} c -- error $ "evaluating unbound term variable: " ++ v
  Lam pi x tau b -> Close (Lam pi x (tm $ eval (Close tau ctx)) 
                              (tm $ eval (Close b $ (x,(Nothing, Close tau ctx)):ctx))) ctx 
  App m n -> case eval $ Close m ctx of 
    Close (Lam False x tau b) ctx' -> eval $ Close b ((x,(Just (Close n ctx), Close tau ctx')):ctx') 
    l -> error $ "Expected function, got: " ++ show l
  _ -> c 

type Context = [(String, (Maybe Closure, Closure))]
type Error = String 
err = Left

data Closure = Close {
  tm :: Term,
  cx :: Context
} deriving (Eq)

instance Show Closure where
  show (Close t ctx) = "<" ++ show t ++ "|" ++ concat (map show ctx) ++ ">"

force :: Closure -> Either Error Closure
force c = let Close t ctx = c in case t of 
  Lam False v t b -> do
    Close b' ctx' <- force =<< infer (Close b ((v,(Nothing, Close t ctx)):ctx))
    return $ Close (Lam True v t b') ctx
  Lam True v t b -> pure c
  Type k -> pure c 
  Var v -> pure c 
  t -> err $ "Forcing non-value: " ++ show t

infer :: Closure -> Either Error Closure
infer c@(Close t ctx) = case {-trace (show c)-} t of
  Var x -> do maybe (err $ "Unbound variable: " ++ x) (pure.snd) (lookup x ctx)
  App m n -> do
    n' <- force =<< infer (Close n ctx)
    Close l ctx' <- infer (Close m ctx)
    case l of
      Lam pi v t b | tm (eval (Close t ctx')) == tm (eval n') -> (if pi then pure else infer) $ Close b ((v,(Just (Close n ctx), n')):ctx')
      Lam pi v t b -> err $ show (tm (eval (Close t ctx'))) ++ " ≠ " ++ show (tm (eval n'))
      e -> err $ "Expected value, got: " ++ show e
  Lam True v t b -> do
    tt <- infer (Close t ctx) 
    bt <- infer (Close b ((v,(Nothing, Close t ctx)):ctx))
    case (tm tt,tm bt) of
      (Type k1, Type k2) -> pure $ Close (Type (max k1 k2)) []
      _ -> err $ "Expected *, *, got: " ++ show (tm tt) ++ ", " ++ show (tm bt)
  _ -> pure c


-- Synthesis takes a type and returns one of three options:
--    1. A term of that type
--    2. A term of not (that type)
--    3. Failure to find either

-- Naive approach :: 
synthesize :: Int -> Term -> Either String [DB.Term]
synthesize n t = case db t of 
  Left s -> Left s 
  Right dbt -> (case filter f $ bfs n of
    [] -> Left "no solutions"
    xs -> Right xs) where  
      f t' = case DB.infer (DB.Close t' []) of
        Left _ -> False
        Right tau -> tau == DB.Close dbt [] || tau == DB.Close (DB.Lam True dbt (DB.Lam True (DB.Type 0) (DB.Var 0))) []

-- Checks all terms of size n to find one that satisfies the condition
bfs :: Int -> [DB.Term]
bfs n = f 0 n where
  f :: Int -> Int -> [DB.Term]
  f i 0 = []
  f i n = map DB.Var [0..(i-1)] ++ 
        map (uncurry (DB.Lam True)) [(tau, b) | tau <- f i (n-1), b <- f (i+1) (n-1)] ++ 
        map (uncurry (DB.Lam False)) [(tau, b) | tau <- f i (n-1), b <- f (i+1) (n-1)] ++ 
        map (uncurry DB.App) [(m, n) | m <- f i (n-1), n <- f i (n-1)] ++ 
        [DB.Type 0]
       
  
{-
infer :: Closure -> [Closure] -> Either Error (Either Closure Closure)
infer c@(Close t ctx) st = case {-trace (show c)-} t of
  Var x ->  do
    (term, ty) <- maybe (err $ "Unbound variable: " ++ x) pure (lookup x ctx)
    case (st, term) of 
      ([], _) -> pure ty 
      (c:cs, Just term) -> infer term st 
      (c:cs, Nothing) -> do
        ct <- eval <$> infer c []
        case eval ty of
          Close (Pi x t b) ctx' | tm (eval (Close t ctx')) == tm ct -> 
            pure $ eval (Close b ((x, (Just c, ct)):ctx')) --err $ "non-empty stack without term to infer for variable: " ++ x
          Close (Pi x t b) ctx' -> err $ show (tm ct) ++ " <> " ++ show (tm (eval (Close t ctx')))
          ty' -> err $ "Expected ∀, got: " ++ show (tm ty')
  App m n -> infer (Close m ctx) (Close n ctx:st) 
  Pi x t b -> do
    tt <- infer (Close t ctx) st
    bt <- infer (Close b ((x,(Nothing, Close t ctx)):ctx)) st
    case (tm tt,tm bt) of
      (Type k1, Type k2) -> pure $ Close (Type (max k1 k2)) []
      _ -> err $ "Expected *, *, got: " ++ show (tm tt) ++ ", " ++ show (tm bt)
  Lam x t b -> do
    tt <- infer (Close t ctx) []
    case tm tt of 
      Type k1 -> case st of
        [] -> flip Close ctx . Pi x t . tm <$> infer (Close b ((x,(Nothing, Close t ctx)):ctx)) st
        c:cs -> do
          ct <- infer c [] 
          let ct' = tm (eval ct) 
          let t' = tm (eval (Close t ctx))
          if ct' == t' 
            then infer (Close b ((x, (Just c, ct)):ctx)) cs
            else err $ show ct' ++ " <> " ++ show t'
      _ -> err $ "Expected *, got: " ++ show tt
  Type k -> pure $ Close (Type k) [] -- todo: universe heirarchy with universe polymorphism
-}

inf :: Term -> Either String Closure
inf t =  eval <$> (force =<< infer (Close t []))

