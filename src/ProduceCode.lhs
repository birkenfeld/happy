-----------------------------------------------------------------------------
The code generator.

(c) 1993-2001 Andy Gill, Simon Marlow
-----------------------------------------------------------------------------

> module ProduceCode (produceParser) where

> import Paths_happy            ( version )
> import Data.Version           ( showVersion )
> import Grammar
> import Target                 ( Target(..) )
> import GenUtils               ( mapDollarDollar, str, char, nl, strspace,
>                                 interleave, interleave', maybestr,
>                                 brack, brack' )

> import Data.Maybe                     ( isJust, isNothing, fromJust )
> import Data.Char
> import Data.List

> import Control.Monad      ( forM_ )
> import Control.Monad.ST
> import Data.Bits          ( setBit )
> import Data.Array.ST      ( STUArray )
> import Data.Array.Unboxed ( UArray )
> import Data.Array.MArray
> import Data.Array.IArray

%-----------------------------------------------------------------------------
Produce the complete output file.

> produceParser :: Grammar                      -- grammar info
>               -> ActionTable                  -- action table
>               -> GotoTable                    -- goto table
>               -> String                       -- stuff to go at the top
>               -> Maybe String                 -- module header
>               -> Maybe String                 -- module trailer
>               -> Target                       -- type of code required
>               -> Bool                         -- use coercions
>               -> Bool                         -- use ghc extensions
>               -> Bool                         -- strict parser
>               -> String

> produceParser (Grammar
>               { productions = prods
>               , non_terminals = nonterms
>               , terminals = terms
>               , types = nt_types
>               , first_nonterm = first_nonterm'
>               , eof_term = eof
>               , first_term = fst_term
>               , token_names = token_names'
>               , lexer = lexer'
>               , imported_identity = imported_identity'
>               , monad = (use_monad,monad_context,monad_tycon,monad_then,monad_return)
>               , token_specs = token_rep
>               , token_type = token_type'
>               , starts = starts'
>               , error_handler = error_handler'
>               , error_sig = error_sig'
>               , attributetype = attributetype'
>               , attributes = attributes'
>               })
>               action goto top_options module_header module_trailer
>               target coerce ghc strict
>     = ( top_opts
>       . maybestr module_header . nl
>       . str comment
>               -- comment goes *after* the module header, so that we
>               -- don't screw up any OPTIONS pragmas in the header.
>       . produceAbsSynDecl . nl
>       . produceTypes
>       . produceActionTable target
>       . produceReductions
>       . produceTokenConverter . nl
>       . produceMonadStuff
>       . produceEntries
>       . maybestr module_trailer . nl
>       ) ""
>  where
>    n_starts = length starts'
>    token = brack token_type'

>    nowarn_opts = str "#![allow(unreachable_patterns)]" . nl
>       -- XXX Happy-generated code is full of warnings.  Some are easy to
>       -- fix, others not so easy, and others would require GHC version
>       -- #ifdefs.  For now I'm just disabling all of them.

>    top_opts = nowarn_opts .
>      case top_options of
>          "" -> str ""
>          _  -> str (unwords [ "{-# OPTIONS"
>                             , top_options
>                             , "#-}"
>                             ]) . nl

%-----------------------------------------------------------------------------
Make the abstract syntax type declaration, of the form:

data HappyAbsSyn a t1 .. tn
        = HappyTerminal a
        | HappyAbsSyn1 t1
        ...
        | HappyAbsSynn tn

>    produceAbsSynDecl
>     | coerce = error "coerce mode not supported"
>     | otherwise
>       = str "#[derive(Clone)]" . nl
>       . str "enum HappyAbsSyn {" . nl
>       . str "    HappyTerminal" . token . str "," . nl
>       . str "    HappyErrorToken(isize)," . nl
>       . interleave "\n"
>         [ str "    " . makeAbsSynCon n . type_param n ty . str ","
>         | (n, ty) <- assocs nt_types,
>           (nt_types_index ! n) == n]
>       . str "}" . nl
>       . str "use self::HappyAbsSyn::*;" . nl . nl

%-----------------------------------------------------------------------------
Type declarations of the form:

type HappyReduction a b = ....
action_0, action_1 :: Int -> HappyReduction a b
reduction_1, ...   :: HappyReduction a b

These are only generated if types for *all* rules are given (and not for array
based parsers -- types aren't as important there).

type Monad<T> = P<T>;
type Token = CToken;

>    produceTypes =
>        str "type Monad<T> = " . str monad_tycon . str "<T>;" . nl
>      . str "type Token = " . token . str ";" . nl

%-----------------------------------------------------------------------------
Next, the reduction functions.   Each one has the following form:

happyReduce_n_m = happyReduce n m reduction where {
   reduction (
        (HappyAbsSynX  | HappyTerminal) happy_var_1 :
        ..
        (HappyAbsSynX  | HappyTerminal) happy_var_q :
        happyRest)
         = HappyAbsSynY
                ( <<user supplied string>> ) : happyRest
        ; reduction _ _ = notHappyAtAll n m

where n is the non-terminal number, and m is the rule number.

NOTES on monad productions.  These look like

        happyReduce_275 = happyMonadReduce 0# 119# happyReduction_275
        happyReduction_275 (happyRest)
                =  happyThen (code) (\r -> happyReturn (HappyAbsSyn r))

why can't we pass the HappyAbsSyn constructor to happyMonadReduce and
save duplicating the happyThen/happyReturn in each monad production?
Because this would require happyMonadReduce to be polymorphic in the
result type of the monadic action, and since in array-based parsers
the whole thing is one recursive group, we'd need a type signature on
happyMonadReduce to get polymorphic recursion.  Sigh.

>    produceReductions =
>       interleave "\n\n"
>          (zipWith produceReduction (drop n_starts prods) [ n_starts .. ])

>    produceReduction (nt, toks, (code,vars_used), _) i

>     | is_monad_prod && (use_monad || imported_identity')
>       = mkReductionHdr (str ", " . showInt lt) monad_reduce False
>       . str "refute! {\nfn " . reductionFun . str "<T>("
>       . stackPattern tokPatterns . str ": HappyStk<HappyAbsSyn>"
>       . str ", tk: T) -> P<HappyAbsSyn> {" . nl
>       . str "    happyThen({"
>       . tokLets (str code') . str " }," . nl
>       . str "              box move |r| happyReturn(" . this_absSynCon . str "(r)))" . nl
>       . str "}" . nl
>       . str "}" . nl

>     | specReduceFun lt
>       = mkReductionHdr id ("happySpecReduce_" ++ show lt) (lt == 0)
>       . str "fn " . reductionFun . str "("
>       . interleave' ", " tokBinds . str ") -> HappyAbsSyn {" . nl
>       . case length tokPatterns of
>          0 ->   str "    "
>               . tokLets (this_absSynCon . char '(' . str code' . str ")") . nl
>          _ ->   str "    match (" . interleave' ", " tokVars . str ") {" . nl
>               . case length tokPatterns of
>                  1 -> str "        " . interleave' ", " tokPatterns . str " => "
>                  _ -> str "        (" . interleave' ", " tokPatterns . str ") => "
>               . tokLets (this_absSynCon . char '(' . str code' . str ")") . char ',' . nl
>               . str "        _ => notHappyAtAll()" . nl
>               . str "    }" . nl
>       . str "}" . nl

>     | otherwise
>       = mkReductionHdr (str ", " . showInt lt) "happyReduce" False
>       . str "refute! {\nfn " . reductionFun . str "("
>       . stackPattern tokPatterns . str ": HappyStk<HappyAbsSyn>"
>       . str ") -> HappyStk<HappyAbsSyn> {" . nl . str "    "
>       . tokLets (str "HappyStk(" . this_absSynCon . char '(' . str code' .
>                  str "), Some(box happyRest))") . nl
>       . str "}" . nl
>       . str "}" . nl

>       where
>               (code', is_monad_prod, _monad_pass_token, monad_reduce)
>                     = case code of
>                         '%':'%':code1 -> (code1, True, True, "happyMonad2Reduce")
>                         '%':'^':_code1 -> error "monadPassToken not supported"
>                                          -- (code1, True, True, "happyMonadReduce")
>                         '%':code1     -> (code1, True, False, "happyMonadReduce")
>                         _ -> (code, False, False, "")

>               -- adjust the nonterminal number for the array-based parser
>               -- so that nonterminals start at zero.
>               adjusted_nt | target == TargetArrayBased = nt - first_nonterm'
>                           | otherwise                  = nt

>               mkReductionHdr lt' s empty =
>                       str "fn " . mkReduceFun i . str "() -> ActionReturn {" . nl
>                       . str "    partial_5!(" . str s
>                       . lt' . str ", " . showInt adjusted_nt . str ", "
>                       . (if empty then reductionFun . str "()" else str "box " . reductionFun)
>                       . str ")\n}" . nl . nl

>               reductionFun = str "happyReduction_" . shows i

>               stackPattern (t:ts) = str "HappyStk(" . t . str ", Some(box "
>                                     . stackPattern ts . str "))"
>               stackPattern []     = str "happyRest"

>               tokPatterns
>                | coerce = reverse (map mkDummyVar [1 .. length toks])
>                | otherwise = reverse (zipWith tokPattern [1..] toks)

>               tokBinds = reverse (map (\v -> mkDummyVar v . str ": HappyAbsSyn") [1 .. length toks])

>               tokVars = reverse (map mkDummyVar [1 .. length toks])

>               tokPattern n _ | n `notElem` vars_used = char '_'
>               tokPattern n t | t >= firstStartTok && t < fst_term
>                       = if coerce
>                               then mkHappyVar n
>                               else makeAbsSynCon t . str "(" . mkHappyVar n . str ")"
>               tokPattern n t
>                       = if coerce
>                               then mkHappyTerminalVar n t
>                               else str "HappyTerminal("
>                                  . mkHappyTerminalVar n t
>                                  . char ')'

>               tokLets code''
>                  | coerce && not (null cases)
>                       = interleave "\n\t" cases
>                       . code'' . str (take (length cases) (repeat '}'))
>                  | otherwise = code''

>               cases = [ str "case " . extract t . strspace . mkDummyVar n
>                       . str " of { " . tokPattern n t . str " -> "
>                       | (n,t) <- zip [1..] toks,
>                         n `elem` vars_used ]

>               extract t | t >= firstStartTok && t < fst_term = mkHappyOut t
>                         | otherwise                     = str "happyOutTok"

>               lt = length toks

>               this_absSynCon | coerce    = mkHappyIn nt
>                              | otherwise = makeAbsSynCon nt

%-----------------------------------------------------------------------------
The token conversion function.

>    produceTokenConverter
>       = case lexer' of {

>       Nothing -> error "no lexer is not supported";

>       Just (lexer'',eof') ->
>           str "fn happyNewToken<T: 'static, S: 'static + Clone>(action: Action<T, S>, "
>         . str "sts: Vec<HappyState<" . token . str ", Box<FnBox(S) -> P<T>>>>, stk: S) -> P<T> {" . nl
>         . str "    let action = Rc::new(action);" . nl
>         . str "    " . str lexer'' . str "(box move |tk: Token| {" . nl
>         . str "        let tk_ = tk.clone();" . nl
>         . str "        let cont = move |i| {" . nl
>         . str "            let action_ = action.clone();" . nl
>         . str "            action(i, i, tk_, HappyState(Rc::new(apply_5_1_clone!(action_))), sts, stk)" . nl
>         . str "        };" . nl
>         . str "        match tk {" . nl
>         . str "            " . str eof' . str " => cont(" . eofTok . str ")," . nl
>         . interleave ",\n" (map doToken token_rep)
>         -- exhaustive already
>         -- . str "            _ => happyError_q(tk.clone())," . nl
>         . str "        }" . nl
>         . str "    })\n}" . nl . nl
>         . str "fn happyError_<T: 'static>(_: isize, tk: " . token . str ") -> P<T> {" . nl
>         . str "    happyError_q(tk)" . nl
>         . str "}" . nl . nl
>       }

>       where
>         eofTok = showInt eof
>         doToken (i,tok)
>               = str "            "
>               . str (removeDollarDollar tok)
>               . str " => cont(" . showInt i . str ")"

Use a variable rather than '_' to replace '$$', so we can use it on
the left hand side of '@'.

>         removeDollarDollar xs = case mapDollarDollar xs of
>                                  Nothing -> xs
>                                  Just fn -> fn "happy_dollar_dollar"

>    mkHappyTerminalVar :: Int -> Int -> String -> String
>    mkHappyTerminalVar i t =
>     case tok_str_fn of
>       Nothing -> pat
>       Just fn -> str (fn (pat []))
>     where
>         tok_str_fn = case lookup t token_rep of
>                     Nothing -> Nothing
>                     Just str' -> mapDollarDollar str'
>         pat = mkHappyVar i

%-----------------------------------------------------------------------------
Action Tables.

Here we do a bit of trickery and replace the normal default action
(failure) for each state with at least one reduction action.  For each
such state, we pick one reduction action to be the default action.
This should make the code smaller without affecting the speed.  It
changes the sematics for errors, however; errors could be detected in
a different state now (but they'll still be detected at the same point
in the token stream).

Further notes on default cases:

Default reductions are important when error recovery is considered: we
don't allow reductions whilst in error recovery, so we'd like the
parser to automatically reduce down to a state where the error token
can be shifted before entering error recovery.  This is achieved by
using default reductions wherever possible.

One case to consider is:

State 345

        con -> conid .                                      (rule 186)
        qconid -> conid .                                   (rule 212)

        error          reduce using rule 212
        '{'            reduce using rule 186
        etc.

we should make reduce_212 the default reduction here.  So the rules become:

   * if there is a production
        error -> reduce_n
     then make reduce_n the default action.
   * if there is a non-reduce action for the error token, the default action
     for this state must be "fail".
   * otherwise pick the most popular reduction in this state for the default.
   * if there are no reduce actions in this state, then the default
     action remains 'enter error recovery'.

This gives us an invariant: there won't ever be a production of the
type 'error -> reduce_n' explicitly in the grammar, which means that
whenever an unexpected token occurs, either the parser will reduce
straight back to a state where the error token can be shifted, or if
none exists, we'll get a parse error.  In theory, we won't need the
machinery to discard states in the parser...

>    produceActionTable TargetHaskell
>       = foldr (.) id (map (produceStateFunction goto) (assocs action))
>    produceActionTable _ = error "array target not supported"

>    produceStateFunction goto' (state, acts)
>       = str "fn " . mkActionName state . str "(i: isize) -> ActionReturn {\n"
>       . str "    match i {\n"
>       . foldr (.) id (map produceActions assocs_acts)
>       . foldr (.) id (map produceGotos   (assocs gotos))
>       . str "        _ => "
>       . mkAction default_act . nl

        . (case default_act of
             LR'Fail -> callHappyExpListPerState
             LR'MustFail -> callHappyExpListPerState
             _ -> str "")

>       . str "    }" . nl . str "}" . nl . nl

>       where gotos = goto' ! state

              callHappyExpListPerState = str " (happyExpListPerState "
                                       . str (show state) . str ")"

>             produceActions (_, LR'Fail{-'-}) = id
>             produceActions (t, action'@(LR'Reduce{-'-} _ _))
>                | action' == default_act = id
>                | otherwise = producePossiblyFailingAction t action'
>             produceActions (t, action')
>               = producePossiblyFailingAction t action'

>             producePossiblyFailingAction t action'
>               = actionFunction t
>               . mkAction action'

                . (case action' of
                    LR'Fail -> str " []"
                    LR'MustFail -> str " []"
                    _ -> str "")

>               . str "," . nl

>             produceGotos (t, Goto i)
>               = actionFunction t
>               . str "partial_5!(happyGoto, curry_1_5!(" . mkActionName i . str ")),\n"
>             produceGotos (_, NoGoto) = id

>             actionFunction t
>               = str "        " . showInt t . str " => "

>             default_act = getDefault assocs_acts

>             assocs_acts = assocs acts

     (_, last_state) = bounds action
     n_states = last_state + 1

>    n_terminals = length terms
>    n_nonterminals = length nonterms - n_starts -- lose %starts

>    (_act_offs,_goto_offs,table,_defaults,_check,explist)
>       = mkTables action goto first_nonterm' fst_term
>               n_terminals n_nonterminals n_starts (bounds token_names')

>    table_size = length table - 1

     n_rules = length prods - 1 :: Int

>    showInt i | ghc       = shows i . showChar '#'
>              | otherwise = shows i

This lets examples like:

        data HappyAbsSyn t1
                = HappyTerminal ( HaskToken )
                | HappyAbsSyn1 (  HaskExp  )
                | HappyAbsSyn2 (  HaskExp  )
                | HappyAbsSyn3 t1

*share* the defintion for ( HaskExp )

        data HappyAbsSyn t1
                = HappyTerminal ( HaskToken )
                | HappyAbsSyn1 (  HaskExp  )
                | HappyAbsSyn3 t1

... cuting down on the work that the type checker has to do.

Note, this *could* introduce lack of polymophism,
for types that have alphas in them. Maybe we should
outlaw them inside { }

>    nt_types_index :: Array Int Int
>    nt_types_index = array (bounds nt_types)
>                       [ (a, fn a b) | (a, b) <- assocs nt_types ]
>     where
>       fn n Nothing = n
>       fn _ (Just a) = case lookup a assoc_list of
>                         Just v -> v
>                         Nothing -> error ("cant find an item in list")
>       assoc_list = [ (b,a) | (a, Just b) <- assocs nt_types ]

>    makeAbsSynCon = mkAbsSynCon nt_types_index

MonadStuff:

  - with no %monad or %lexer:

        happyThen    :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
        happyReturn  :: () => a -> HappyIdentity a
        happyThen1   m k tks = happyThen m (\a -> k a tks)
        happyReturn1 = \a tks -> happyReturn a

  - with %monad:

        happyThen    :: CONTEXT => P a -> (a -> P b) -> P b
        happyReturn  :: CONTEXT => a -> P a
        happyThen1   m k tks = happyThen m (\a -> k a tks)
        happyReturn1 = \a tks -> happyReturn a

  - with %monad & %lexer:

        happyThen    :: CONTEXT => P a -> (a -> P b) -> P b
        happyReturn  :: CONTEXT => a -> P a
        happyThen1   = happyThen
        happyReturn1 = happyReturn


>    produceMonadStuff =
>            let pcont = str monad_context
>                pty = str monad_tycon  in
>            str "fn happyThen<A: 'static, B: 'static>(m: " . pty . str "<A>, "
>          . str "f: Box<FnBox(A) -> " . pty . str "<B>>) -> " . pty . str "<B> {" . nl
>          . str "    thenP(m, f)" . nl
>          . str "}" . nl
>          . str "fn happyReturn<A: 'static>(v: A) -> " . pty . str "<A> {" . nl
>          . str "    returnP(v)" . nl
>          . str "}" . nl
>          . case lexer' of
>               Nothing -> error "no lexer is not supported"
>               _ ->
>                  str "fn happyThen1<A: 'static, B: 'static>(m: " . pty . str "<A>, "
>                . str "f: Box<FnBox(A) -> " . pty . str "<B>>) -> " . pty . str "<B> {" . nl
>                . str "    thenP(m, f)" . nl
>                . str "}" . nl
>                . str "fn happyReturn1<A: 'static>(v: A) -> " . pty . str "<A> {" . nl
>                . str "    returnP(v)" . nl
>                . str "}" . nl
>                . str "fn happyError_q<A: 'static>(tk: " . token . str ") -> " . pty . str "<A> {" . nl
>                . str "    // TODO" . nl
>                . str "    happyError()" . nl
>                . str "}" . nl . nl

An error handler specified with %error is passed the current token
when used with %lexer, but happyError (the old way but kept for
compatibility) is not passed the current token. Also, the %errorhandlertype
directive determins the API of the provided function.

>    errorHandler =
>       case error_handler' of
>               Just h  -> case error_sig' of
>                              ErrorHandlerTypeExpList -> str h
>                              ErrorHandlerTypeDefault -> str "(\\(tokens, _) -> " . str h . str " tokens)"
>               Nothing -> case lexer' of
>                               Nothing -> str "(\\(tokens, _) -> happyError tokens)"
>                               Just _  -> str "(\\(tokens, explist) -> happyError)"

-----------------------------------------------------------------------------
-- Produce the parser entry and exit points

>    produceEntries
>       = interleave "\n" (map produceEntry (zip starts' [0..]))
>       . if null attributes' then id else produceAttrEntries starts'

>    produceEntry :: ((String, t0, Int, t1), Int) -> String -> String
>    produceEntry ((name, _start_nonterm, accept_nonterm, _partial), no)
>       = str "fn "
>       . (if null attributes' then str name else str "do_" . str name)
>       . str "() -> " . str monad_tycon . str "<" . str nt_type . str "> {" . nl
>       . str "    happyThen(happyParse(curry_1_5!(" . str "action_" . shows no
>       . str ")), box |x| match x {" . nl
>       . str "        HappyAbsSyn" . shows (nt_types_index ! accept_nonterm)
>       . str "(z) => happyReturn(z)," . nl
>       . str "        _ => notHappyAtAll()" . nl
>       . str "    })" .nl
>       . str "}" . nl
>      where
>        nt_type = fromJust . fromJust . lookup accept_nonterm . assocs $ nt_types

>    produceAttrEntries starts''
>       = interleave "\n\n" (map f starts'')
>     where
>       f = case (use_monad,lexer') of
>             (True,Just _)  -> \(name,_,_,_) -> monadAndLexerAE name
>             (True,Nothing) -> \(name,_,_,_) -> monadAE name
>             (False,Just _) -> error "attribute grammars not supported for non-monadic parsers with %lexer"
>             (False,Nothing)-> \(name,_,_,_) -> regularAE name

>       defaultAttr = fst (head attributes')

>       monadAndLexerAE name
>         = str name . str " = "
>         . str "do { "
>         . str "f <- do_" . str name . str "; "
>         . str "let { (conds,attrs) = f happyEmptyAttrs } in do { "
>         . str "sequence_ conds; "
>         . str "return (". str defaultAttr . str " attrs) }}"
>       monadAE name
>         = str name . str " toks = "
>         . str "do { "
>         . str "f <- do_" . str name . str " toks; "
>         . str "let { (conds,attrs) = f happyEmptyAttrs } in do { "
>         . str "sequence_ conds; "
>         . str "return (". str defaultAttr . str " attrs) }}"
>       regularAE name
>         = str name . str " toks = "
>         . str "let { "
>         . str "f = do_" . str name . str " toks; "
>         . str "(conds,attrs) = f happyEmptyAttrs; "
>         . str "x = foldr seq attrs conds; "
>         . str "} in (". str defaultAttr . str " x)"

-----------------------------------------------------------------------------
Replace all the $n variables with happy_vars, and return a list of all the
vars used in this piece of code.

> actionVal :: LRAction -> Int
> actionVal (LR'Shift  state _) = state + 1
> actionVal (LR'Reduce rule _)  = -(rule + 1)
> actionVal LR'Accept           = -1
> actionVal (LR'Multiple _ a)   = actionVal a
> actionVal LR'Fail             = 0
> actionVal LR'MustFail         = 0

> mkAction :: LRAction -> String -> String
> mkAction (LR'Shift i _)       = str "partial_5!(happyShift, curry_1_5!(" . mkActionName i . str "))"
> mkAction LR'Accept            = str "box happyAccept"
> mkAction LR'Fail              = str "box happyFail"
> mkAction LR'MustFail          = str "box happyFail"
> mkAction (LR'Reduce i _)      = str "happyReduce_" . shows i . str "()"
> mkAction (LR'Multiple _ a)    = mkAction a

> mkActionName :: Int -> String -> String
> mkActionName i                = str "action_" . shows i

See notes under "Action Tables" above for some subtleties in this function.

> getDefault :: [(Name, LRAction)] -> LRAction
> getDefault actions =
>   -- pick out the action for the error token, if any
>   case [ act | (e, act) <- actions, e == errorTok ] of

>       -- use error reduction as the default action, if there is one.
>       act@(LR'Reduce _ _) : _                 -> act
>       act@(LR'Multiple _ (LR'Reduce _ _)) : _ -> act

>       -- if the error token is shifted or otherwise, don't generate
>       --  a default action.  This is *important*!
>       (act : _) | act /= LR'Fail -> LR'Fail

>       -- no error actions, pick a reduce to be the default.
>       _      -> case reduces of
>                     [] -> LR'Fail
>                     (act:_) -> act    -- pick the first one we see for now

>   where reduces
>           =  [ act | (_,act@(LR'Reduce _ _)) <- actions ]
>           ++ [ act | (_,(LR'Multiple _ act@(LR'Reduce _ _))) <- actions ]

-----------------------------------------------------------------------------
-- Generate packed parsing tables.

-- happyActOff ! state
--     Offset within happyTable of actions for state

-- happyGotoOff ! state
--     Offset within happyTable of gotos for state

-- happyTable
--      Combined action/goto table

-- happyDefAction ! state
--      Default action for state

-- happyCheck
--      Indicates whether we should use the default action for state


-- the table is laid out such that the action for a given state & token
-- can be found by:
--
--        off    = happyActOff ! state
--        off_i  = off + token
--        check  | off_i => 0 = (happyCheck ! off_i) == token
--               | otherwise  = False
--        action | check      = happyTable ! off_i
--               | otherwise  = happyDefAaction ! off_i


-- figure out the default action for each state.  This will leave some
-- states with no *real* actions left.

-- for each state with one or more real actions, sort states by
-- width/spread of tokens with real actions, then by number of
-- elements with actions, so we get the widest/densest states
-- first. (I guess the rationale here is that we can use the
-- thin/sparse states to fill in the holes later, and also we
-- have to do less searching for the more complicated cases).

-- try to pair up states with identical sets of real actions.

-- try to fit the actions into the check table, using the ordering
-- from above.


> mkTables
>        :: ActionTable -> GotoTable -> Name -> Int -> Int -> Int -> Int -> (Int, Int) ->
>        ([Int]         -- happyActOffsets
>        ,[Int]         -- happyGotoOffsets
>        ,[Int]         -- happyTable
>        ,[Int]         -- happyDefAction
>        ,[Int]         -- happyCheck
>        ,[Int]         -- happyExpList
>        )

> mkTables action goto first_nonterm' fst_term
>               n_terminals n_nonterminals n_starts
>               token_names_bound

>  = ( elems act_offs,
>      elems goto_offs,
>      take max_off (elems table),
>      def_actions,
>      take max_off (elems check),
>      elems explist
>   )
>  where

>        (table,check,act_offs,goto_offs,explist,max_off)
>                = runST (genTables (length actions)
>                         max_token token_names_bound
>                         sorted_actions explist_actions)

>        -- the maximum token number used in the parser
>        max_token = max n_terminals (n_starts+n_nonterminals) - 1

>        def_actions = map (\(_,_,def,_,_,_) -> def) actions

>        actions :: [TableEntry]
>        actions =
>                [ (ActionEntry,
>                   state,
>                   actionVal default_act,
>                   if null acts'' then 0
>                        else fst (last acts'') - fst (head acts''),
>                   length acts'',
>                   acts'')
>                | (state, acts) <- assocs action,
>                  let (err:_dummy:vec) = assocs acts
>                      vec' = drop (n_starts+n_nonterminals) vec
>                      acts' = filter (notFail) (err:vec')
>                      default_act = getDefault acts'
>                      acts'' = mkActVals acts' default_act
>                ]

>        explist_actions :: [(Int, [Int])]
>        explist_actions = [ (state, concat $ map f $ assocs acts)
>                          | (state, acts) <- assocs action ]
>                          where
>                            f (t, LR'Shift _ _ ) = [t - fst token_names_bound]
>                            f (_, _) = []

>        -- adjust terminals by -(fst_term+1), so they start at 1 (error is 0).
>        --  (see ARRAY_NOTES)
>        adjust token | token == errorTok = 0
>                     | otherwise         = token - fst_term + 1

>        mkActVals assocs' default_act =
>                [ (adjust token, actionVal act)
>                | (token, act) <- assocs'
>                , act /= default_act ]

>        gotos :: [TableEntry]
>        gotos = [ (GotoEntry,
>                   state, 0,
>                   if null goto_vals then 0
>                        else fst (last goto_vals) - fst (head goto_vals),
>                   length goto_vals,
>                   goto_vals
>                  )
>                | (state, goto_arr) <- assocs goto,
>                let goto_vals = mkGotoVals (assocs goto_arr)
>                ]

>        -- adjust nonterminals by -first_nonterm', so they start at zero
>        --  (see ARRAY_NOTES)
>        mkGotoVals assocs' =
>                [ (token - first_nonterm', i) | (token, Goto i) <- assocs' ]

>        sorted_actions = reverse (sortBy cmp_state (actions++gotos))
>        cmp_state (_,_,_,width1,tally1,_) (_,_,_,width2,tally2,_)
>                | width1 < width2  = LT
>                | width1 == width2 = compare tally1 tally2
>                | otherwise = GT

> data ActionOrGoto = ActionEntry | GotoEntry
> type TableEntry = (ActionOrGoto,
>                       Int{-stateno-},
>                       Int{-default-},
>                       Int{-width-},
>                       Int{-tally-},
>                       [(Int,Int)])

> genTables
>        :: Int                         -- number of actions
>        -> Int                         -- maximum token no.
>        -> (Int, Int)                  -- token names bounds
>        -> [TableEntry]                -- entries for the table
>        -> [(Int, [Int])]              -- expected tokens lists
>        -> ST s (UArray Int Int,       -- table
>                 UArray Int Int,       -- check
>                 UArray Int Int,       -- action offsets
>                 UArray Int Int,       -- goto offsets
>                 UArray Int Int,       -- expected tokens list
>                 Int                   -- highest offset in table
>           )

> genTables n_actions max_token token_names_bound entries explist = do

>   table      <- newArray (0, mAX_TABLE_SIZE) 0
>   check      <- newArray (0, mAX_TABLE_SIZE) (-1)
>   act_offs   <- newArray (0, n_actions) 0
>   goto_offs  <- newArray (0, n_actions) 0
>   off_arr    <- newArray (-max_token, mAX_TABLE_SIZE) 0
>   exp_array  <- newArray (0, (n_actions * n_token_names + 15) `div` 16) 0

>   max_off <- genTables' table check act_offs goto_offs off_arr exp_array entries
>                       explist max_token n_token_names

>   table'     <- freeze table
>   check'     <- freeze check
>   act_offs'  <- freeze act_offs
>   goto_offs' <- freeze goto_offs
>   exp_array' <- freeze exp_array
>   return (table',check',act_offs',goto_offs',exp_array',max_off+1)

>   where
>        n_states = n_actions - 1
>        mAX_TABLE_SIZE = n_states * (max_token + 1)
>        (first_token, last') = token_names_bound
>        n_token_names = last' - first_token + 1


> genTables'
>        :: STUArray s Int Int          -- table
>        -> STUArray s Int Int          -- check
>        -> STUArray s Int Int          -- action offsets
>        -> STUArray s Int Int          -- goto offsets
>        -> STUArray s Int Int          -- offset array
>        -> STUArray s Int Int          -- expected token list
>        -> [TableEntry]                -- entries for the table
>        -> [(Int, [Int])]              -- expected tokens lists
>        -> Int                         -- maximum token no.
>        -> Int                         -- number of token names
>        -> ST s Int                    -- highest offset in table

> genTables' table check act_offs goto_offs off_arr exp_array entries
>            explist max_token n_token_names
>       = fill_exp_array >> fit_all entries 0 1
>   where

>        fit_all [] max_off _ = return max_off
>        fit_all (s:ss) max_off fst_zero = do
>          (off, new_max_off, new_fst_zero) <- fit s max_off fst_zero
>          ss' <- same_states s ss off
>          writeArray off_arr off 1
>          fit_all ss' new_max_off new_fst_zero

>        fill_exp_array =
>          forM_ explist $ \(state, tokens) ->
>            forM_ tokens $ \token -> do
>              let bit_nr = state * n_token_names + token
>              let word_nr = bit_nr `div` 16
>              let word_offset = bit_nr `mod` 16
>              x <- readArray exp_array word_nr
>              writeArray exp_array word_nr (setBit x word_offset)

>        -- try to merge identical states.  We only try the next state(s)
>        -- in the list, but the list is kind-of sorted so we shouldn't
>        -- miss too many.
>        same_states _ [] _ = return []
>        same_states s@(_,_,_,_,_,acts) ss@((e,no,_,_,_,acts'):ss') off
>          | acts == acts' = do writeArray (which_off e) no off
>                               same_states s ss' off
>          | otherwise = return ss

>        which_off ActionEntry = act_offs
>        which_off GotoEntry   = goto_offs

>        -- fit a vector into the table.  Return the offset of the vector,
>        -- the maximum offset used in the table, and the offset of the first
>        -- entry in the table (used to speed up the lookups a bit).
>        fit (_,_,_,_,_,[]) max_off fst_zero = return (0,max_off,fst_zero)

>        fit (act_or_goto, state_no, _deflt, _, _, state@((t,_):_))
>           max_off fst_zero = do
>                -- start at offset 1 in the table: all the empty states
>                -- (states with just a default reduction) are mapped to
>                -- offset zero.
>          off <- findFreeOffset (-t+fst_zero) check off_arr state
>          let new_max_off | furthest_right > max_off = furthest_right
>                          | otherwise                = max_off
>              furthest_right = off + max_token

>          -- trace ("fit: state " ++ show state_no ++ ", off " ++ show off ++ ", elems " ++ show state) $ do

>          writeArray (which_off act_or_goto) state_no off
>          addState off table check state
>          new_fst_zero <- findFstFreeSlot check fst_zero
>          return (off, new_max_off, new_fst_zero)

When looking for a free offest in the table, we use the 'check' table
rather than the main table.  The check table starts off with (-1) in
every slot, because that's the only thing that doesn't overlap with
any tokens (non-terminals start at 0, terminals start at 1).

Because we use 0 for LR'MustFail as well as LR'Fail, we can't check
for free offsets in the main table because we can't tell whether a
slot is free or not.

> -- Find a valid offset in the table for this state.
> findFreeOffset :: Int -> STUArray s Int Int -> STUArray s Int Int -> [(Int, Int)] -> ST s Int
> findFreeOffset off table off_arr state = do
>     -- offset 0 isn't allowed
>   if off == 0 then try_next else do

>     -- don't use an offset we've used before
>   b <- readArray off_arr off
>   if b /= 0 then try_next else do

>     -- check whether the actions for this state fit in the table
>   ok <- fits off state table
>   if not ok then try_next else return off
>  where
>       try_next = findFreeOffset (off+1) table off_arr state


> fits :: Int -> [(Int,Int)] -> STUArray s Int Int -> ST s Bool
> fits _   []           _     = return True
> fits off ((t,_):rest) table = do
>   i <- readArray table (off+t)
>   if i /= -1 then return False
>              else fits off rest table

> addState :: Int -> STUArray s Int Int -> STUArray s Int Int -> [(Int, Int)]
>          -> ST s ()
> addState _   _     _     [] = return ()
> addState off table check ((t,val):state) = do
>    writeArray table (off+t) val
>    writeArray check (off+t) t
>    addState off table check state

> notFail :: (Int, LRAction) -> Bool
> notFail (_, LR'Fail) = False
> notFail _           = True

> findFstFreeSlot :: STUArray s Int Int -> Int -> ST s Int
> findFstFreeSlot table n = do
>        i <- readArray table n
>        if i == -1 then return n
>                   else findFstFreeSlot table (n+1)

-----------------------------------------------------------------------------
-- Misc.

> comment :: String
> comment =
>         "\n// Parser produced by modified Happy Version " ++ showVersion version ++ "\n\n"

> mkAbsSynCon :: Array Int Int -> Int -> String -> String
> mkAbsSynCon fx t      = str "HappyAbsSyn"   . shows (fx ! t)

> mkHappyVar, mkReduceFun, mkDummyVar :: Int -> String -> String
> mkHappyVar n          = str "happy_var_"    . shows n
> mkReduceFun n         = str "happyReduce_"  . shows n
> mkDummyVar n          = str "happy_x_"      . shows n

> mkHappyIn, mkHappyOut :: Int -> String -> String
> mkHappyIn n           = str "happyIn"  . shows n
> mkHappyOut n          = str "happyOut" . shows n

> type_param :: Int -> Maybe String -> ShowS
> type_param n Nothing   = char 't' . shows n
> type_param _ (Just ty) = brack ty

> specReduceFun :: Int -> Bool
> specReduceFun = (<= 3)

-----------------------------------------------------------------------------
-- Convert an integer to a 16-bit number encoded in \xNN\xNN format suitable
-- for placing in a string.

> hexChars :: [Int] -> String
> hexChars acts = concat (map hexChar acts)

> hexChar :: Int -> String
> hexChar i | i < 0 = hexChar (i + 65536)
> hexChar i =  toHex (i `mod` 256) ++ toHex (i `div` 256)

> toHex :: Int -> String
> toHex i = ['\\','x', hexDig (i `div` 16), hexDig (i `mod` 16)]

> hexDig :: Int -> Char
> hexDig i | i <= 9    = chr (i + ord '0')
>          | otherwise = chr (i - 10 + ord 'a')
