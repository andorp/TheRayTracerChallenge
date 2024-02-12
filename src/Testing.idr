module Testing

import Decidable.Equality

data Tag = G | W | T | D

public export
data Story : Tag -> Tag -> (Type -> Type) -> Type -> Type where
  Bind  : (Story t1 t2 m a) -> (a -> Story t2 t3 m b) -> Story t1 t3 m b
  Given : a -> Story t G m a
  When  : String -> (m (Dec a)) -> Story t W m a
  Then  : String -> m Bool -> Story t T m ()
  Fail  : String -> Story t1 t2 m ()
  Done  : Story t1 D m ()

export
pure : a -> Story t1 G m a
pure  = Given

export
(>>=) : (Story t1 t2 m a) -> (a -> Story t2 t3 m b) -> Story t1 t3 m b
(>>=) = Bind

TestCaseM : {t : Tag} -> (Type -> Type) -> Type
TestCaseM {t} m = Story t D m ()

public export
TestCase : {t : Tag} -> Type
TestCase {t} = Story t D Prelude.id ()

record Eval (m,n : Type -> Type) where
  constructor MkEval
  check : String -> m Bool -> n ()
  pure  : forall a . a -> n a
  bind  : forall a , b . n a -> (a -> n b) -> n b
  embed : forall a . m a -> n a
  fail  : forall a . String -> n a

eval : Eval m n -> (Story t1 t2 m a) -> n a
eval e (Given x  ) = e.pure x
eval e (Bind  x k) = e.bind (eval e x) (eval e . k)
eval e (When  m x) =
  e.bind
    (e.embed x)
    (\case
      Yes a => e.pure a
      No  _ => e.fail m)
eval e (Then  m x) = e.check m x
eval e (Fail  m  ) = e.fail m
eval e Done        = e.pure ()

data TestResult : Type -> Type where
  Error : String -> TestResult a
  Ok    : a -> TestResult a

renderTestResult : TestResult () -> String
renderTestResult (Error str) = "Error! - " ++ str
renderTestResult (Ok _)      = "Passed!"

pureEval : Eval Prelude.id TestResult
pureEval = MkEval
  { check = \m , b => if b then Ok () else Error m
  , pure  = Ok
  , bind  = \case
              (Error str) => \f => Error str
              (Ok x)      => \f => f x
  , embed = Ok
  , fail  = Error
  }

export
test : String -> TestCase -> IO ()
test name t = putStrLn $ name ++ " > " ++ renderTestResult (eval pureEval t)

