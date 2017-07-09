#ifdef HAPPY_GHC
compile_error!("GHC mode is not supported")
#endif

#define ILIT(n) (n)
#define IBOX(n) (n)
#define FAST_INT Int
#define LT(n,m) (n < m)
#define GTE(n,m) (n >= m)
#define EQ(n,m) (n == m)
#define PLUS(n,m) (n + m)
#define MINUS(n,m) (n - m)
#define TIMES(n,m) (n * m)
#define NEGATE(n) (negate (n))
#define IF_GHC(x)

#if defined(HAPPY_ARRAY)
#define CONS(h,t) (HappyCons (h) (t))
#else
#define CONS(h,t) ((h):(t))
#endif

#if defined(HAPPY_ARRAY)
#define ERROR_TOK ILIT(0)
#define DO_ACTION(state,i,tk,sts,stk) happyDoAction i tk state sts (stk)
#define HAPPYSTATE(i) (i)
#define GOTO(action) happyGoto
#define IF_ARRAYS(x) (x)
#else
#define ERROR_TOK ILIT(1)
#define DO_ACTION(state,i,tk,sts,stk) state i i tk HAPPYSTATE(state) sts (stk)
#define HAPPYSTATE(i) (HappyState (i))
#define GOTO(action) action
#define IF_ARRAYS(x)
#endif

#if defined(HAPPY_COERCE)
#define GET_ERROR_TOKEN(x)  (case Happy_GHC_Exts.unsafeCoerce# x of { IBOX(i) -> i })
#define MK_ERROR_TOKEN(i)   (Happy_GHC_Exts.unsafeCoerce# IBOX(i))
#define MK_TOKEN(x)         (happyInTok (x))
#else
#define GET_ERROR_TOKEN(x)  (case x of { HappyErrorToken IBOX(i) -> i })
#define MK_ERROR_TOKEN(i)   (HappyErrorToken IBOX(i))
#define MK_TOKEN(x)         (HappyTerminal (x))
#endif

#if defined(HAPPY_DEBUG)
#define DEBUG_TRACE(s)    (happyTrace (s)) $
happyTrace string expr = Happy_System_IO_Unsafe.unsafePerformIO $ do
    Happy_System_IO.hPutStr Happy_System_IO.stderr string
    return expr
#else
#define DEBUG_TRACE(s)    {- nothing -}
#endif

#[derive(Clone)]
pub struct HappyStk<a>(a, Option<Box<HappyStk<a>>>);

// -----------------------------------------------------------------------------
/// starting the parse
fn happyParse(start_state: Box<Fn(isize, isize, CToken, HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>, Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>>, HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>) -> P<HappyAbsSyn> {
    // TODO this is lazy failure
    happyNewToken(start_state, vec![], HappyStk(HappyAbsSyn::HappyErrorToken(0), None))
}

// -----------------------------------------------------------------------------
/// Accepting the parse
///
/// If the current token is ERROR_TOK, it means we've just accepted a partial
/// parse (a %partial parser).  We must ignore the saved token on the top of
/// the stack in this case.
fn happyAccept(_0: isize, _1: CToken, _2: HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>, _3: Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>>, _4: HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn> {
    match (_0, _1, _2, _3, _4) {
        (1, tk, st, sts, HappyStk(_, Some(box HappyStk(ans, _)))) => {
            happyReturn1(ans)
        },
        (j, tk, st, sts, HappyStk(ans, _)) => {
            (happyReturn1(ans))
        },
    }
}

// -----------------------------------------------------------------------------
/// HappyState data type (not arrays)
pub struct HappyState<b, c>(Rc<Box<Fn(isize, isize, b, HappyState<b, c>, Vec<HappyState<b, c>>) -> c>>);

impl<b, c> Clone for HappyState<b, c> {
    fn clone(&self) -> Self {
        HappyState(self.0.clone())
    }
}

// -----------------------------------------------------------------------------
/// Shifting a token
fn happyShift(_0: Box<Fn(isize, isize, CToken, HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>, Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>>, HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>, _1: isize, _2: CToken, _3: HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>, _4: Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>>, _5: HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn> {
    match (_0, _1, _2, _3, _4, _5) {
        (new_state, 1, tk, st, sts, stk) => {
            {
                let HappyStk(x, _) = stk.clone();
                let i = (match x {
                        HappyErrorToken(i) => {
                            i
                        },
                        _ => unreachable!(),
                    });

            let new_state = Rc::new(new_state);
            let new_state_ = new_state.clone();
            new_state(i, i, tk, (HappyState(Rc::new(apply_5_1_clone!(new_state_)))), (__op_concat(st, sts)), stk)            }
        },
        (new_state, i, tk, st, sts, stk) => {
            happyNewToken(new_state, (__op_concat(st, sts)), (HappyStk((HappyTerminal(tk)), Some(box stk))))
        },
    }
}

// happyReduce is specialised for the common cases.

fn happySpecReduce_0(_0: isize, _1: HappyAbsSyn, _2: isize, _3: CToken, _4: HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>, _5: Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>>, _6: HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn> {
    match (_0, _1, _2, _3, _4, _5, _6) {
        (i, __fn, 1, tk, st, sts, stk) => {
            happyFail( (1), tk, st, sts, stk)
        },
        (nt, __fn, j, tk, st, sts, stk) => {
            let HappyState(action) = st.clone();
            action(nt, j, tk, st.clone(), (__op_concat(st, sts)))((HappyStk(__fn, Some(box stk))))
        },
    }
}

fn happySpecReduce_1(_0: isize, _1: Box<Fn(HappyAbsSyn) -> HappyAbsSyn>, _2: isize, _3: CToken, _4: HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>, _5: Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>>, _6: HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn> {
    match (_0, _1, _2, _3, _4, _5, _6) {
        (i, __fn, 1, tk, st, sts, stk) => {
            happyFail((1), tk, st, sts, stk)
        },
        (nt, __fn, j, tk, _, sts, HappyStk(v1, stk_q)) => {
            {
                // TODO assert len > 0?
                let st = sts.clone().remove(0);
                let HappyState(action) = st.clone();
                let r = __fn(v1);

            happySeq(r.clone(), (action(nt, j, tk, st, sts)((HappyStk(r, stk_q)))))            }
        },
    }
}

fn happySpecReduce_2(_0: isize, _1: Box<Fn(HappyAbsSyn, HappyAbsSyn) -> HappyAbsSyn>, _2: isize, _3: CToken, _4: HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>, _5: Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>>, _6: HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn> {
    match (_0, _1, _2, _3, _4, _5, _6) {
        (i, __fn, 1, tk, st, sts, stk) => {
            happyFail( (1), tk, st, sts, stk)
        },
        (nt, __fn, j, tk, _, mut sts, HappyStk(v1, Some(box HappyStk(v2, Some(box stk_q))))) => {
            {
                sts.remove(0);
                let st = sts.clone().remove(0);
                let HappyState(action) = st.clone();

                let r = __fn(v1, v2);

            happySeq(r.clone(), (action(nt, j, tk, st, sts)((HappyStk(r, Some(box stk_q))))))            }
        },
        _ => {
            panic!("IRREFUTABLE PATTERN")
        }
    }
}

fn happySpecReduce_3(_0: isize, _1: Box<Fn(HappyAbsSyn, HappyAbsSyn, HappyAbsSyn) -> HappyAbsSyn>, _2: isize, _3: CToken, _4: HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>, _5: Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>>, _6: HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn> {
    match (_0, _1, _2, _3, _4, _5, _6) {
        (i, __fn, 1, tk, st, sts, stk) => {
            happyFail( (1), tk, st, sts, stk)
        },
        (nt, __fn, j, tk, _, mut stses, HappyStk(v1, Some(box HappyStk(v2, Some(box HappyStk(v3, stk_q)))))) => {
            {
                stses.remove(0);
                stses.remove(0);
                let sts = stses.clone();
                let st = stses.clone().remove(0);
                let HappyState(action) = st.clone();

                let r = __fn(v1, v2, v3);

            happySeq(r.clone(), (action(nt, j, tk, st, sts)(HappyStk(r, stk_q))))            }
        },
        _ => {
            panic!("IRREFUTABLE PATTERN");
        }
    }
}

fn happyReduce<a00: 'static>(_0: isize, _1: isize, _2: Box<Fn(HappyStk<HappyAbsSyn>) -> HappyStk<HappyAbsSyn>>, _3: isize, _4: CToken, _5: HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<a00>>>, _6: Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<a00>>>>, _7: HappyStk<HappyAbsSyn>) -> P<a00> {
    match (_0, _1, _2, _3, _4, _5, _6, _7) {
        (k, i, __fn, 1, tk, st, sts, stk) => {
            happyFail( (1), tk, st, sts, stk)
        },
        (k, nt, __fn, j, tk, st, sts, stk) => {
            match happyDrop(((k - ((1)))), sts) {
                sts1 => {
                    {
                        let st1 = sts1.clone().remove(0);
                        let HappyState(action) = st1.clone();

                        // it doesn't hurt to always seq here...
                        let r = __fn(stk);

                    happyDoSeq(r.clone(), (action(nt, j, tk, st1, sts1)(r)))                    }
                },
            }
        },
    }
}

fn happyMonadReduce<b00: 'static>(_0: isize, _1: isize, _2: Box<Fn(HappyStk<HappyAbsSyn>, CToken) -> P<HappyAbsSyn>>, _3: isize, _4: CToken, _5: HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<b00>>>, _6: Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<b00>>>>, _7: HappyStk<HappyAbsSyn>) -> P<b00> {
    match (_0, _1, _2, _3, _4, _5, _6, _7) {
        (k, nt, __fn, 1, tk, st, sts, stk) => {
            happyFail((1), tk, st, sts, stk)
        },
        (k, nt, __fn, j, tk, st, sts, stk) => {
            match happyDrop(k, (__op_concat(st, sts))) {
                sts1 => {
                    {
                        let st1 = sts1.clone().remove(0);
                        let HappyState(action) = st1.clone();

                        let drop_stk = happyDropStk(k, stk.clone());

                    happyThen1((__fn(stk.clone(), tk.clone())), (box move |r| { clones!(sts1, drop_stk, st1, tk);
                        action(nt, j, tk, st1, sts1)((HappyStk(r, Some(box drop_stk)))) }))                    }
                },
            }
        },
    }
}

fn happyMonad2Reduce<b00: 'static, t0>(_0: isize, _1: t0, _2: Box<Fn(HappyStk<HappyAbsSyn>, CToken) -> P<HappyAbsSyn>>, _3: isize, _4: CToken, _5: HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<b00>>>, _6: Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<b00>>>>, _7: HappyStk<HappyAbsSyn>) -> P<b00> {
    match (_0, _1, _2, _3, _4, _5, _6, _7) {
        (k, nt, __fn, 1, tk, st, sts, stk) => {
            happyFail( (1), tk, st, sts, stk)
        },
        (k, nt, __fn, j, tk, st, sts, stk) => {
            match happyDrop(k, (__op_concat(st, sts))) {
                sts1 => { {
                        let st1 = sts1.clone().remove(0);
                        let HappyState(action) = st1.clone();

                        let drop_stk = happyDropStk(k, stk.clone());

                        let new_state = action;

                    happyThen1(__fn(stk, tk),
                        box move |r| { clones!(drop_stk, sts1, new_state);
                            happyNewToken(curry_5_1!(new_state), sts1, (HappyStk(r, Some(box drop_stk))))
                        }
                    ) }
                },
            }
        },
    }
}

fn happyDrop<t0>(_0: isize, _1: Vec<t0>) -> Vec<t0> {
    match (_0, _1) {
        (0, l) => {
            l
        },
        (n, mut t) => {
            t.remove(0); // TODO this can panic, how does Haskell do this
            happyDrop(((n - ((1)))), t)
        },
    }
}

fn happyDropStk<t0>(_0: isize, _1: HappyStk<t0>) -> HappyStk<t0> {
    match (_0, _1) {
        (0, l) => {
            l
        },
        (n, HappyStk(x, Some(box xs))) => {
            happyDropStk(((n - ((1)))), xs)
        },
        _ => {
            panic!("REFUTABLE PATTERN");
        }
    }
}

// -----------------------------------------------------------------------------
/// Moving to a new state after a reduction
fn happyGoto(action: Box<Fn(isize, isize, CToken, HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>, Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>>, HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>, j: isize, tk: CToken, st: HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>, _curry_4: Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn>>>>, _curry_5: HappyStk<HappyAbsSyn>) -> P<HappyAbsSyn> {
    let action = Rc::new(action);
    let action_ = action.clone();
    action(j, j, tk, (HappyState(Rc::new(apply_5_1_clone!(action_)))), _curry_4, _curry_5)
}

// -----------------------------------------------------------------------------
/// Error recovery (ERROR_TOK is the error token)
fn happyFail<a0: 'static>(_0: isize, _1: CToken, _2: HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<a0>>>, _3: Vec<HappyState<CToken, Box<Fn(HappyStk<HappyAbsSyn>) -> P<a0>>>>, _4: HappyStk<HappyAbsSyn>) -> P<a0> {
    match (_0, _1, _2, _3, _4) {
        (1, tk, old_st, _, HappyStk(x, Some(_))) => {
            {
                let i = (match x {
                        HappyErrorToken(i) => {
                            i
                        },
                        _ => unreachable!(),
                    });

            happyError_(i, tk)            }
        },
        (i, tk, HappyState(action), sts, stk) => {
            action((1), (1), tk, (HappyState(action.clone())), sts)((HappyStk((HappyErrorToken(i)), Some(box stk))))
        },
    }
}

fn notHappyAtAll<a: 'static>() -> a {
    panic!("Internal Happy error")
}

fn happySeq<a, b>(a: a, b: b) -> b {
    seq(a, b)
}

fn happyDoSeq<a, b>(a: a, b: b) -> b {
    seq(a, b)
}

fn happyDontSeq<a, b>(a: a, b: b) -> b {
    b
}

// end of Happy Template.
