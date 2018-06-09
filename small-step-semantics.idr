||| Modeling the small-step (structural) operational semantics from the book
||| "Semantics with Applications" by Hanne Riis Nielson and Flemming Nielson

%default total

||| type of expression in While
data Ty = TyInt | TyBool

interpTy : Ty -> Type
interpTy TyInt  = Int
interpTy TyBool = Bool

||| expression in While
data Expr : Ty -> Type where
  ||| int literal
  ILit : Int -> Expr TyInt
  ||| boolean literal
  BLit : Bool -> Expr TyBool
  ||| plus
  Add  : Expr TyInt -> Expr TyInt -> Expr TyInt
  ||| minus
  Sub  : Expr TyInt -> Expr TyInt -> Expr TyInt
  ||| less-than
  Lt   : Expr TyInt -> Expr TyInt -> Expr TyBool
  ||| equals
  Equ  : (Eq (interpTy t)) => Expr t -> Expr t -> Expr TyBool
  ||| int variable
  IVar : String -> Expr TyInt
  ||| boolean variable
  BVar : String -> Expr TyBool

||| a statement in While
data Stmt : Type where
  ||| does nothing
  Skip : Stmt
  ||| assignment to a variable
  Ass  : String -> Expr a -> Stmt
  ||| if-then-else
  ITE  : Expr TyBool -> Stmt -> Stmt -> Stmt
  ||| while loop
  While : Expr TyBool -> Stmt -> Stmt
  ||| statement composition
  Comp  : Stmt -> Stmt -> Stmt

||| program state
State : Type
State = List (String, Either Int Bool)

||| a semantic configuration
||| it is either intermediate <S,s>
||| or a terminated state s
data Conf : Type where
  ||| a terminal state
  Term   : State -> Conf
  Interm : Stmt -> State -> Conf

||| evaluation of an expression of While in a state s.
||| We hack our way out of it and just return default
||| values if we cannot look up variables in the state.
eval : Expr t -> State -> interpTy t
eval (ILit x) s = x
eval (BLit x) s = x
eval (Add x y) s = eval x s + eval y s
eval (Sub x y) s = eval x s - eval y s
eval (Lt x y) s = eval x s < eval y s
eval (Equ x y) s = eval x s == eval y s
eval (IVar n) s =
  case lookup n s of
       Just (Left x)  => x
       _ => 0
eval (BVar n) s =
  case lookup n s of
       Just (Right x) => x
       _ => False

||| Assign an expression to a variable, returning an updated state
pushVar : (String, Expr t) -> State -> State
pushVar (v, e) s {t = TyInt}  = (v, Left $ eval e s) :: s
pushVar (v, e) s {t = TyBool} = (v, Right $ eval e s) :: s

||| A semantic transition between two configurations.
||| These correspond to the axioms of small-step operational semantics
data Trans : Conf -> Conf -> Type where
  ||| skip does nothing
  TSkip  : (s:State) -> Trans (Interm Skip s) (Term s)
  ||| assignment terminates in a state s with the assigned expression in it
  TAss   : (s:State) -> Trans (Interm (Ass v e) s) (Term (pushVar (v,e) s))
  ||| composition of two statements, where the first does not terminate in one step
  TComp1 : Trans (Interm w1 s) (Interm w1' s') -> Trans (Interm (Comp w1 w2) s) (Interm (Comp w1' w2) s')
  ||| composition of two statements, where the first *does* terminate in one step
  TComp2 : Trans (Interm w1 s) (Term s') -> Trans (Interm (Comp w1 w2) s) (Interm w2 s')
  ||| Evaluation of if-then-else in a state where eval b s = True
  TITEtt : (s:State) -> eval b s = True  -> Trans (Interm (ITE b w1 w2) s) (Interm w1 s)
  ||| Evaluation of if-then-else in a state where eval b s = False
  TITEff : (s:State) -> eval b s = False -> Trans (Interm (ITE b w1 w2) s) (Interm w2 s)
  ||| Step a while loop by translating it to a while statement
  TWhile : (s:State) -> Trans (Interm (While b w1) s) (Interm (ITE b (Comp w1 (While b w1)) Skip) s)

||| Construct a transition from a statement and a state, based on the evaluation
||| function
transStmt : (w:Stmt) -> (s:State) -> (c ** Trans (Interm w s) c)
transStmt Skip s = (_ ** TSkip s)
transStmt (Ass x y) s = (_ ** TAss s)
transStmt (ITE b y z) s with (eval b s) proof p
  | False = (_ ** TITEff _ (sym p))
  | True  = (_ ** TITEtt _ (sym p))
transStmt (While x y) s = (_ ** TWhile s)
transStmt (Comp w1 w2) s with (transStmt w1 s)
  | ((Term s') ** pf) = (_ ** TComp2 pf)
  | ((Interm w1' s') ** pf) = (_ ** TComp1 pf)

||| A derivation sequence in the small-step semantics of While.
||| derivations *always* terminate in our model.
||| non-termination is expressed as a contradiction
data DerivSeq : Conf -> Nat -> Conf -> Type where
  ||| the zero-length derivation
  Nil  : DerivSeq gamma Z gamma
  (::) : Trans (Interm w1 s) gamma
      -> DerivSeq gamma n gamma'
      -> DerivSeq (Interm w1 s) (S n) gamma'

syntax "<" [w] "," [s] ">" "=>" [k] [gamma] = DerivSeq (Interm w s) k gamma;

||| If <w1;w2, s> =>k s'' then there exists k1, k2, s' such that
||| <w1, s> =>k1 s' and <w2,s'> =>k2 s'' and k = k1 + k2
lemma_2_19 : <Comp w1 w2, s> =>k (Term s'')
          -> (k1 ** k2 ** s' ** (<w1, s> =>k1 (Term s'), <w2, s'> =>k2 (Term s''), k = k1 + k2 ))
lemma_2_19 ((TComp1 x) :: y) with (lemma_2_19 y)
  lemma_2_19 ((TComp1 x) :: y) | (ik1 ** ik2 ** is ** (iseq1, iseq2, iprf)) =
    ((S ik1) ** ik2 ** is ** (x :: iseq1, iseq2, cong iprf))
lemma_2_19 ((TComp2 x) :: y) = ((S Z) ** _ ** _ ** ([x], y, Refl))

||| If <w1,s> =>k s' then <w1;w2, s> =>k <w2, s'>
lemma_2_21 : <w1,s> =>k (Term s')
          -> <Comp w1 w2,s> =>k (Interm w2 s')
lemma_2_21 (x :: []) {w2} {s} = [TComp2 x]
lemma_2_21 (x :: (y :: z)) {w2} with (lemma_2_21 {w2=w2} (y :: z))
  lemma_2_21 (x :: (y :: z)) | (w :: s) = (TComp1 x) :: w :: s


||| If <w,s> =>(S k) y then there exists w' and s' such that
||| <w,s> =>k <w',s'> =>1 y
last : <w,s> =>(S k) y
    -> (w' ** s' ** (<w,s> =>k (Interm w' s'), <w',s'> =>(S Z) y))
last {w} {s} [x]           = (w ** s ** ([], [x]))
last (x :: y :: z) =
  let (w' ** s' ** (h, t)) = last (y :: z)
  in  (w' ** s' ** (x :: h, t))


iteff : Trans (Interm (ITE b w1 w2) s) y1 -> (False = eval b s) -> (y1 = Interm w2 s)
iteff (TITEtt s x) prf = void $ trueNotFalse (sym $ trans prf x)
iteff (TITEff s x) prf = Refl

itett : Trans (Interm (ITE b w1 w2) s) y1 -> (True = eval b s) -> (y1 = Interm w1 s)
itett (TITEff s x) prf = void $ trueNotFalse (trans prf x)
itett (TITEtt s x) prf = Refl

iteffderiv : <ITE b w1 w2, s> =>(S n) y1 -> (False = eval b s) -> <w2, s> =>n y1
iteffderiv (x :: y) prf =
  let Refl = iteff x prf
  in  y

itettderiv : <ITE b w1 w2, s> =>(S n) y1 -> (True = eval b s) -> <w1, s> =>n y1
itettderiv (x :: y) prf =
  let Refl = itett x prf
  in  y

-- Lets start proving determinism of our semantics

||| ITE has determinsitic semantics
determITE : <ITE b w1 w2, s> =>(S Z) y1 -> <ITE b w1 w2, s> =>(S Z) y2 -> y1 = y2
determITE {b} {s} x y with (eval b s) proof p
  determITE {b = b} {s = s} [x] [y] | False =
    let Refl = iteff x p
        p' = iteff y p
    in  sym p'
  determITE {b = b} {s = s} [x] [y] | True =
    let Refl = itett x p
        p'   = itett y p
    in  sym p'

||| We'll need to know that a transition (one-step derivation) are deterministic,
||| and here we prove the converse
transUnique : Trans (Interm w s) (Interm w' s') -> Trans (Interm w s) (Term s'') -> Void
transUnique (TComp1 _) (TSkip _) impossible
transUnique (TComp1 _) (TAss _) impossible
transUnique (TComp1 _) (TComp1 _) impossible
transUnique (TComp1 _) (TComp2 _) impossible
transUnique (TComp1 _) (TITEtt _ _) impossible
transUnique (TComp1 _) (TITEff _ _) impossible
transUnique (TComp1 _) (TWhile _) impossible
transUnique (TComp2 _) (TSkip _) impossible
transUnique (TComp2 _) (TAss _) impossible
transUnique (TComp2 _) (TComp1 _) impossible
transUnique (TComp2 _) (TComp2 _) impossible
transUnique (TComp2 _) (TITEtt _ _) impossible
transUnique (TComp2 _) (TITEff _ _) impossible
transUnique (TComp2 _) (TWhile _) impossible
transUnique (TITEtt _ _) (TSkip _) impossible
transUnique (TITEtt _ _) (TAss _) impossible
transUnique (TITEtt _ _) (TComp1 _) impossible
transUnique (TITEtt _ _) (TComp2 _) impossible
transUnique (TITEtt _ _) (TITEtt _ _) impossible
transUnique (TITEtt _ _) (TITEff _ _) impossible
transUnique (TITEtt _ _) (TWhile _) impossible
transUnique (TITEff _ _) (TSkip _) impossible
transUnique (TITEff _ _) (TAss _) impossible
transUnique (TITEff _ _) (TComp1 _) impossible
transUnique (TITEff _ _) (TComp2 _) impossible
transUnique (TITEff _ _) (TITEtt _ _) impossible
transUnique (TITEff _ _) (TITEff _ _) impossible
transUnique (TITEff _ _) (TWhile _) impossible
transUnique (TWhile _) (TSkip _) impossible
transUnique (TWhile _) (TAss _) impossible
transUnique (TWhile _) (TComp1 _) impossible
transUnique (TWhile _) (TComp2 _) impossible
transUnique (TWhile _) (TITEtt _ _) impossible
transUnique (TWhile _) (TITEff _ _) impossible
transUnique (TWhile _) (TWhile _) impossible

||| Skip is obviously deterministic
determSkip : DerivSeq (Interm Skip s) (S Z) (Term s) -> DerivSeq (Interm Skip s) (S Z) (Term s) -> s = s
determSkip [(TSkip s)] [(TSkip s)] = Refl

||| Assign is obviously deterministic
determAss : DerivSeq (Interm (Ass v e) s) (S Z) (Term s')
          -> DerivSeq (Interm (Ass v e) s) (S Z) (Term s'') -> s' = s''
determAss [(TAss s)] [(TAss s)] = Refl

--- We need mutual recursion to prove that composition is deterministic
mutual
  determComp : DerivSeq (Interm (Comp w1 w2) s) (S Z) y1 -> DerivSeq (Interm (Comp w1 w2) s) (S Z) y2 -> y1 = y2
  determComp [(TComp1 x)] [(TComp1 y)] =
    let Refl = determStep [x] [y] in Refl
  determComp [(TComp1 x)] [(TComp2 y)] = void $ transUnique x y
  determComp [(TComp2 x)] [(TComp1 y)] = void $ transUnique y x
  determComp [(TComp2 x)] [(TComp2 y)] =
    let Refl = determStep [x] [y] in Refl

  determStep : DerivSeq (Interm w s) (S Z) y1 -> DerivSeq (Interm w s) (S Z) y2 -> y1 = y2
  determStep [TSkip s] [TSkip s] {w = Skip} = Refl
  determStep [TAss _] [TAss _] {w = (Ass v e)} = Refl
  determStep [x] [y] {w = (Comp w1 w2)} = determComp [x] [y]
  determStep [x] [y] {w = (ITE b w1 w2)} = determITE [x] [y]
  determStep [(TWhile s)] [(TWhile s)] {w = (While b w1)} = Refl

||| Determinism of the small-step semantics, that is:
||| If <w1, s> =>k s' and <w1, s'> =>k s'' then s' = s''
deterministic : DerivSeq (Interm w1 s) k (Term s') -> DerivSeq (Interm w1 s) k' (Term s'') -> s' = s''
deterministic (h1 :: t1) (h2 :: t2) with (determStep [h1] [h2])
  deterministic (h1 :: []) (h2 :: []) | Refl = Refl
  deterministic (h1 :: (t1h :: t1)) (h2 :: (t2h :: t2)) | Refl =
    deterministic (t1h :: t1) (t2h :: t2)


-- If <w,s> =>m s' and <w,s> =>n s' then n = m
lengthDeterm : DerivSeq w m (Term s') -> DerivSeq w n (Term s') -> (n = m)
lengthDeterm [] [] = Refl
lengthDeterm (x :: xs) (y :: ys) =
  let Refl = determStep [x] [y]
      ih   = lengthDeterm xs ys
  in  cong ih

-- bi-implication
data Iff : Type -> Type -> Type where
  MkIff : (a -> b) -> (b -> a) -> Iff a b

syntax [x] "<->" [y] = Iff x y;

||| deprecated: not needed
implementation Uninhabited (<w,s> =>0 (Term s')) where
  uninhabited [] impossible
  uninhabited (_ :: _) impossible

||| deprecated: not needed
implementation Uninhabited (<While b w,s> =>1 (Term s')) where
  uninhabited ((TWhile _) :: []) impossible
  uninhabited ((TWhile _) :: (_ :: _)) impossible

||| A derivation where we don't care about the number of steps.
||| Corresponds to `<w,s> =>* gamma` in the book
data ExistsDeriv : Stmt -> State -> Conf -> Type where
  MkExistsDeriv : (k ** <w,s> =>k gamma) -> ExistsDeriv w s gamma

||| an infinite derivation sequence. <w,s> => ... if for any state s' and nat k
||| you can prove that <w,s> =>k s' is a contradiction
data InfDeriv : Stmt -> State -> Type where
  MkInfDeriv : (s : State)
            -> ((s' : State) -> (k : Nat) -> <w,s> =>k (Term s') -> Void)
            -> InfDeriv w s

namespace WhileTrueInfinite
  -- Lets exercise our definition of infinite derivations by proving that
  -- While True do w always leads to an infinite derivation

  ||| A while-true statement helper
  while_true : Stmt -> Stmt
  while_true w = While (BLit True) w

  ||| A helper lemma we will need.
  ||| If (1+k) = m + n, then k = (m-1) + n OR k = m + (n-1)
  skIsPlusPred_m_or_n : S k = plus m n -> Either (k = plus (pred m) n) (k = plus m (pred n))
  skIsPlusPred_m_or_n {m = Z} prf = Right (cong {f=Prelude.Nat.pred} prf)
  skIsPlusPred_m_or_n {m = (S m')} {k} {n} prf =
    Left (succInjective k (plus m' n) prf)

  ||| if 0 = plus m n then m = 0 and n = 0
  plusEqZeroIsZero : (0 = plus m n) -> (m = 0, n = 0)
  plusEqZeroIsZero {m = Z} Refl = (Refl, Refl)
  plusEqZeroIsZero {m = (S _)} Refl impossible

  ||| If (m-1) <= k then m <= (k+1)
  ltePred : LTE (pred m) k -> LTE m (S k)
  ltePred {m = Z} prf = LTEZero
  ltePred {m = S m'} prf = LTESucc prf

  ||| If k = m + n then m <= k AND n <= k
  nSumLTE : {k, m, n : Nat} -> k = plus m n -> (m `LTE` k, n `LTE` k)
  nSumLTE {k = Z} prf with (plusEqZeroIsZero prf)
    | (Refl, Refl) = (LTEZero, LTEZero)
  nSumLTE {k = (S k)} {m} {n} prf =
    case skIsPlusPred_m_or_n prf of
      Left l =>
        let (ih1, ih2) = nSumLTE {m=pred m} {n=n} l
        in  (ltePred ih1, lteSuccRight ih2)
      Right r =>
        let (ih1, ih2) = nSumLTE {m=m} {n=pred n} r
        in  (lteSuccRight ih1, ltePred ih2)


  ||| A SUPER annoying lemma that we need to write to convince Idris of what
  ||| seems like an obvious fact.
  destruct_while : (seq : <While b w, s> =>k (Term s'))
                -> ( k'
                    ** iftrans : (<ITE b (Comp w (While b w)) Skip, s> =>(S k') (Term s'))
                    ** (seq = ((TWhile s) :: iftrans), k = (S (S k')))
                  )
  destruct_while ((TSkip  _ ) :: _) impossible
  destruct_while ((TAss   _ ) :: _) impossible
  destruct_while ((TComp1 _) :: _) impossible
  destruct_while ((TComp2 _) :: _) impossible
  destruct_while ((TITEtt _ _) :: _) impossible
  destruct_while ((TITEff _ _) :: _) impossible
  destruct_while ((TWhile s) :: (TSkip  _ ) :: _) impossible
  destruct_while ((TWhile s) :: (TAss   _ ) :: _) impossible
  destruct_while ((TWhile s) :: (TComp1 _) :: _) impossible
  destruct_while ((TWhile s) :: (TComp2 _) :: _) impossible
  destruct_while {k = (S (S k0))} ((TWhile s) :: ((TITEtt s prf) :: y)) =
    (k0 ** ((TITEtt s prf) :: y) ** (Refl, Refl))
  destruct_while {k = (S (S k0))} ((TWhile s) :: ((TITEff s prf) :: y)) =
    (k0 ** ((TITEff s prf) :: y) ** (Refl, Refl))

  ||| A helper function for proof that while (true) do w does not terminate
  ||| We use the sized induction principle, since we cannot otherwise convince
  ||| Idris that our recursion is well-founded, since it relies of lemma_2_19
  ||| splitting up the derivation sequence
  while_true_ind : (k : Nat) -> (w : Stmt) -> (s, s' : State) -> <while_true w, s> => k (Term s') -> Void
  while_true_ind k = sizeInd {P=P} while_step k where
    P : (k : Nat) -> Type
    P k = (w : Stmt) -> (s, s' : State) -> <while_true w, s> => k (Term s') -> Void

    while_step k' rec w s s' xs =
      let (k'' ** tl ** (Refl, Refl)) = destruct_while xs
      in  case tl of
        ((TITEtt s prf) :: tl') =>
          let (k1 ** k2 ** s'' ** (seq1, seq2, kprf)) = lemma_2_19 tl'
              (_, lteprf) = nSumLTE kprf
          in  rec k2 (lteSuccRight (LTESucc lteprf)) _ _ _ seq2
        ((TITEff s prf) :: tl') => trueNotFalse prf
        ((TSkip  _ ) :: _) impossible
        ((TAss   _ ) :: _) impossible
        ((TComp1 _) :: _) impossible
        ((TComp2 _) :: _) impossible
        ((TWhile _) :: _) impossible


  ||| Forall s and w `while (true) do w` has an infinite derivation seq
  while_true_inf : (s : State) -> (w : Stmt) -> InfDeriv (while_true w) s
  while_true_inf s w = MkInfDeriv s (\s', k => while_true_ind k w s s')

  ||| We can also prove our end goal using a much easier method, but it relies
  ||| on the unsafe assert_smaller to coerce Idris' termination checker
  ||| First a helper function
  while_true_help : (s, s' : State) -> (k : Nat) -> <while_true w, s> => k (Term s') -> Void
  while_true_help _ _ Z [] impossible
  while_true_help _ _ (S Z) ((TSkip _) :: []) impossible
  while_true_help _ _ (S Z) ((TAss _) :: []) impossible
  while_true_help _ _ (S Z) ((TComp1 _) :: []) impossible
  while_true_help _ _ (S Z) ((TComp2 _) :: []) impossible
  while_true_help _ _ (S Z) ((TITEtt _ _) :: []) impossible
  while_true_help _ _ (S Z) ((TITEff _ _) :: []) impossible
  while_true_help _ _ (S Z) ((TWhile _) :: []) impossible
  while_true_help s s' (S (S k)) seq@((TWhile s) :: ((TITEtt s _) :: tl)) =
    let (k1 ** k2 ** s'' ** (seq1, seq2, Refl)) = lemma_2_19 tl
    in  while_true_help _ _ _ (assert_smaller seq seq2) -- assert smaller here!
  while_true_help _ _' (S (S _)) ((TWhile _) :: ((TITEff _ Refl) :: _)) impossible

  ||| And then the proof
  while_true_inf' : (s : State) -> (w : Stmt) -> InfDeriv (while_true w) s
  while_true_inf' s w = MkInfDeriv s (\s', k => while_true_help s s' k)



||| two statements w1 and w2 are semantically equivalent if
||| - <w1,s> =>* s' iff <w2,s> =>* s'  and
||| - <w1,s> => ... iff <w2,s> => ...
data SemEquiv : Stmt -> Stmt -> Type where
  MkSemEquiv : ((s, s' : State)
                 -> (ExistsDeriv w1 s (Term s')) <-> (ExistsDeriv w2 s (Term s'))
               )
            -> ((s : State) -> (InfDeriv w1 s) <-> (InfDeriv w2 s))
            -> SemEquiv w1 w2


||| We can append two sequences if one derives to the other
append_seq : DerivSeq y1 k1 y2 -> DerivSeq y2 k2 y3 -> DerivSeq y1 (k1 + k2) y3
append_seq [] [] = []
append_seq [] (x :: y) = (x :: y)
append_seq {k1 = S n} (x :: y) [] = rewrite plusZeroRightNeutral n in (x :: y)
append_seq (h1 :: t1) (h2 :: t2) =
  let ih = append_seq t1 (h2 :: t2)
  in  h1 :: ih

||| Composing w1 and w2 gives us a new sequence that is their sequences appended
comp_right_seq : <w1,s> =>k1 (Term s') -> <w2,s'> =>k2 gamma
              -> <Comp w1 w2, s> =>(k1 + k2) gamma
comp_right_seq {w2} seq1 seq2 =
  let h = lemma_2_21 {w2=w2} seq1
  in  append_seq h seq2

||| A simple lemma
skip_deriv : DerivSeq (Interm Skip s) k1 (Term s') -> (s = s', k1 = 1)
skip_deriv ((TSkip s') :: []) = (Refl, Refl)

||| forall w, w;skip and w are semantically equivalent
wskip_SemEquiv_w : SemEquiv (Comp w1 Skip) w1
wskip_SemEquiv_w =
  MkSemEquiv
    (\s, s' => MkIff (r2lderiv s s') (l2rderiv s s'))
    (\s => MkIff (r2linf s) (l2rlinf s))
  where
    r2lderiv s s' (MkExistsDeriv (k1 ** hyp)) =
      let (k2 ** k3 ** s'' ** (seq1, seq2, prf)) = lemma_2_19 hyp
          (Refl, Refl) = skip_deriv seq2
      in  MkExistsDeriv (_ ** seq1)

    l2rderiv s s' (MkExistsDeriv (k1 ** hyp)) =
      let comp = lemma_2_21 {w2=Skip} hyp
      in  MkExistsDeriv (_ ** (append_seq comp [TSkip s']))

    r2linf s (MkInfDeriv s ih) = MkInfDeriv s prf where
      prf s' k seq =
        let comp_prf = comp_right_seq seq [TSkip s']
        in  ih s' (plus k 1) comp_prf

    l2rlinf s (MkInfDeriv s ih) = MkInfDeriv s prf where
      prf s' k seq =
        let (k1' ** k2' ** s'' ** (seq1, seq2, Refl)) = lemma_2_19 seq
        in  ih s'' k1' seq1
