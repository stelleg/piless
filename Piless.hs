module Piless where
import Debug.Trace

data Term = Var String 
          | Pi String Term Term
          | Lam String Term Term
          | Type N 
          | App Term Term
          deriving (Eq)

instance Show Term where
  show (Lam v tau b) = "λ" ++ v ++ ":" ++ show tau ++ "." ++ show b 
  show (Pi v tau b) = "∀" ++ v ++ ":" ++ show tau ++ "," ++ show b 
  show (App m n) = "(" ++ show m ++ " " ++ show n ++ ")"
  show (Type n) = "*"
  show (Var v) = v

subst :: String -> Term -> Term -> Term
subst x t e = case e of
  Var v | x == v -> t
  Pi v t' b -> Pi v (subst x t t') $ if x /= v then subst x t b else b
  Lam v t' b -> Lam v (subst x t t') $ if x /= v then subst x t b else b
  App m n -> App (subst x t m) (subst x t n)
  _ -> e

eval :: Closure -> Closure
eval c@(Close t ctx) = case t of
  Var v -> case lookup v ctx of
    Nothing -> error ("unbound variable lookup " ++ show v) --error $ "Unbound variable in evaluation: " ++ v 
    Just (Just c, _) -> eval c
    Just (Nothing, _) -> {-trace ("context only type for " ++ v)-} c -- error $ "evaluating unbound term variable: " ++ v
  Lam x tau b -> Close (Lam x (tm $ eval (Close tau ctx)) 
                              (tm $ eval (Close b $ (x,(Nothing, Close tau ctx)):ctx))) ctx 
  Pi x tau b -> Close (Pi x (tm $ eval (Close tau ctx)) 
                            (tm $ eval (Close b $ (x,(Nothing, Close tau ctx)):ctx))) ctx 
  App m n -> case eval $ Close m ctx of 
    Close (Lam x tau b) ctx' -> eval $ Close b ((x,(Just (Close n ctx), Close tau ctx')):ctx') 
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
  Lam v t b -> do
    Close b' ctx' <- force =<< infer (Close b ((v,(Nothing, Close t ctx)):ctx))
    return $ Close (Pi v t b') ctx
  Type k -> pure c 
  Pi v t b -> pure c 
  Var v -> pure c 
  t -> err $ "Forcing non-value: " ++ show t

infer :: Closure -> Either Error Closure
infer c@(Close t ctx) = case {-trace (show c)-} t of
  Var x -> do maybe (err $ "Unbound variable: " ++ x) (pure.snd) (lookup x ctx)
  App m n -> do
    n' <- force =<< infer (Close n ctx)
    Close l ctx' <- infer (Close m ctx)
    case l of
      Pi v t b | tm (eval (Close t ctx')) == tm (eval n') -> pure $ Close b ((v,(Just (Close n ctx), n')):ctx')
      Pi v t b -> err $ show (tm (eval (Close t ctx'))) ++ " <> " ++ show (tm (eval n'))
      Lam v t b | tm (eval (Close t ctx')) == tm (eval n') -> infer (Close b ((v,(Just (Close n ctx), n')):ctx'))
      Lam v t b -> err $ show (tm (eval (Close t ctx'))) ++ " <> " ++ show (tm (eval n'))
      e -> err $ "Expected value, got: " ++ show e
  Pi v t b -> do
    tt <- infer (Close t ctx) 
    bt <- infer (Close b ((v,(Nothing, Close t ctx)):ctx))
    case (tm tt,tm bt) of
      (Type k1, Type k2) -> pure $ Close (Type (max k1 k2)) []
      _ -> err $ "Expected *, *, got: " ++ show (tm tt) ++ ", " ++ show (tm bt)
  _ -> pure c

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

data N = Z | S N

instance Num N where
  fromInteger 0 = Z
  fromInteger n = S $ fromInteger $ pred n
  abs = id
  Z + n = n
  S n + m = S (n + m)
  Z * n = Z
  S Z * n = n
  S n * m = (n * m) + m
  signum = const 1
  negate = id
  Z - n = Z
  n - Z = n
  S n - S m = n - m

instance Eq N where
  S m == S n = m == n
  Z == S n = False
  S n == Z = False
  Z == Z = True

instance Ord N where
  compare (S n) (S m) = compare n m
  compare Z (S n) = LT
  compare (S n) Z = GT
  compare Z Z = EQ

instance Enum N where
  succ = S
  pred (S n) = n
  pred Z = Z
  toEnum 0 = Z
  toEnum n = S $ toEnum $ pred n
  fromEnum (S n) = 1 + fromEnum n
  fromEnum Z = 0

instance Show N where
  show = show . fromEnum 
  
  



