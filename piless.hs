import Debug.Trace

data Term = Var String 
          | Lam String Term Term
          | Type N 
          | App Term Term
          deriving (Eq)

lam v = Lam v (Type Z) 
instance Show Term where
  show (Lam v tau b) = "λ" ++ v ++ ":" ++ show tau ++ "." ++ show b 
  show (App m n) = "(" ++ show m ++ " " ++ show n ++ ")"
  show (Type n) = "Type" ++ show n
  show (Var v) = v

subst :: String -> Term -> Term -> Term
subst x t e = case e of
  Var v | x == v -> t
  Lam v t' b | x /= v -> Lam v (subst x t t') (subst x t b)
  App m n -> App (subst x t m) (subst x t n)
  _ -> e

eval :: Term -> Term
eval t = case t of
  Lam x tau b -> Lam x tau (eval b)
  App m n -> case eval m of Lam x tau b -> eval (subst x n b)
  _ -> t

type Context = [(String, Term)]

infer :: Context -> Term -> Term 
infer ctx t = case t of
  Var x -> maybe (error $ "Unbound variable: " ++ x) id $ lookup x ctx
  Lam x t b -> case (infer ctx t, infer ((x,t):ctx) b) of
    (Type k1, Type k2) -> Type (max k1 k2)
    (Type k1, tau) -> Lam x t tau
    (tt, bt) -> error $ "Expected universe, got: " ++ show tt
  App m n -> case (infer ctx m, infer ctx n) of
    (Lam x t b, nt) | eval t == eval nt -> subst x n b
    (Lam x t b, nt) -> error $ show t ++ " <> " ++ show nt
    (mt, nt) -> error $ "Expected forall, got: " ++ show mt 
  Type k -> Type $ S k

check :: Term -> Term
check = infer []

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
  

--infer :: String -> Term -> Term
--infer s t =   
  



