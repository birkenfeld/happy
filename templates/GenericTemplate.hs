// -----------------------------------------------------------------------------
// HappyStk data type
#[derive(Clone)]
struct HappyStk<a>(a, Option<Box<HappyStk<a>>>);

// -----------------------------------------------------------------------------
// HappyState data type
struct HappyState<T, F>(Rc<Box<Fn(isize, isize, T, HappyState<T, F>, Vec<HappyState<T, F>>) -> F>>);

impl<T, F> Clone for HappyState<T, F> {
    fn clone(&self) -> Self {
        HappyState(self.0.clone())
    }
}

// some convenient typedefs

type Stack = HappyStk<HappyAbsSyn>;
type State<T> = HappyState<Token, Box<FnBox(Stack) -> Monad<T>>>;

type ActionReturn = Box<FnBox(isize, Token, State<HappyAbsSyn>, Vec<State<HappyAbsSyn>>, Stack)
                        -> Monad<HappyAbsSyn>>;

type Action<A, B> = Box<Fn(isize, isize, Token, HappyState<Token, Box<FnBox(B) -> Monad<A>>>,
                           Vec<HappyState<Token, Box<FnBox(B) -> Monad<A>>>>, B) -> Monad<A>>;


// -----------------------------------------------------------------------------
// starting the parse
fn happyParse(start_state: Action<HappyAbsSyn, Stack>) -> Monad<HappyAbsSyn> {
    // TODO this is lazy failure
    happyNewToken(start_state, vec![], HappyStk(HappyAbsSyn::HappyErrorToken(0), None))
}

// -----------------------------------------------------------------------------
// Accepting the parse
//
// If the current token is ERROR_TOK, it means we've just accepted a partial
// parse (a %partial parser).  We must ignore the saved token on the top of
// the stack in this case.
fn happyAccept(j: isize, tk: Token, st: State<HappyAbsSyn>, sts: Vec<State<HappyAbsSyn>>,
               stk: Stack) -> Monad<HappyAbsSyn> {
    match (j, stk) {
        (1, HappyStk(_, Some(box HappyStk(ans, _)))) => happyReturn1(ans),
        (j, HappyStk(ans, _)) => happyReturn1(ans),
    }
}

// -----------------------------------------------------------------------------
// Shifting a token
fn happyShift(new_state: Action<HappyAbsSyn, Stack>, _1: isize, tk: Token,
              st: State<HappyAbsSyn>, sts: Vec<State<HappyAbsSyn>>, stk: Stack) -> Monad<HappyAbsSyn> {
    match _1 {
        1 => {
            let HappyStk(x, _) = stk.clone();
            let i = (match x {
                HappyErrorToken(i) => {
                    i
                },
                _ => unreachable!(),
            });

            let new_state = Rc::new(new_state);
            let new_state_ = new_state.clone();
            new_state(i, i, tk, (HappyState(Rc::new(apply_5_1_clone!(new_state_)))), __op_concat(st, sts), stk)
        }
        i => {
            happyNewToken(new_state, __op_concat(st, sts), (HappyStk(HappyTerminal(tk), Some(box stk))))
        },
    }
}

// happyReduce is specialised for the common cases.

fn happySpecReduce_0(nt: isize, __fn: HappyAbsSyn, _2: isize, tk: Token,
                     st: State<HappyAbsSyn>, sts: Vec<State<HappyAbsSyn>>, stk: Stack) -> Monad<HappyAbsSyn> {
    match _2 {
        1 => happyFail(1, tk, st, sts, stk),
        j => {
            let HappyState(action) = st.clone();
            action(nt, j, tk, st.clone(), __op_concat(st, sts))(HappyStk(__fn, Some(box stk)))
        },
    }
}

fn happySpecReduce_1(nt: isize, __fn: Box<FnBox(HappyAbsSyn) -> HappyAbsSyn>, _2: isize, tk: Token,
                     st: State<HappyAbsSyn>, sts: Vec<State<HappyAbsSyn>>, stk: Stack) -> Monad<HappyAbsSyn> {
    match (_2, stk) {
        (1, stk) => happyFail(1, tk, st, sts, stk),
        (j, HappyStk(v1, stk_q)) => {
            // TODO assert len > 0?
            let st = sts.clone().remove(0);
            let HappyState(action) = st.clone();
            let r = __fn(v1);

            action(nt, j, tk, st, sts)(HappyStk(r, stk_q))
        }
    }
}

fn happySpecReduce_2(nt: isize, __fn: Box<FnBox(HappyAbsSyn, HappyAbsSyn) -> HappyAbsSyn>,
                     _2: isize, tk: Token, st: State<HappyAbsSyn>, mut sts: Vec<State<HappyAbsSyn>>,
                     stk: Stack) -> Monad<HappyAbsSyn> {
    match (_2, stk) {
        (1, stk) => happyFail(1, tk, st, sts, stk),
        (j, HappyStk(v1, Some(box HappyStk(v2, Some(box stk_q))))) => {
            sts.remove(0);
            let st = sts.clone().remove(0);
            let HappyState(action) = st.clone();
            let r = __fn(v1, v2);
            action(nt, j, tk, st, sts)(HappyStk(r, Some(box stk_q)))
        },
        _ => {
            panic!("irrefutable pattern")
        }
    }
}

fn happySpecReduce_3(nt: isize, __fn: Box<FnBox(HappyAbsSyn, HappyAbsSyn, HappyAbsSyn) -> HappyAbsSyn>,
                     _2: isize, tk: Token, st: State<HappyAbsSyn>, mut stses: Vec<State<HappyAbsSyn>>,
                     stk: Stack) -> Monad<HappyAbsSyn> {
    match (_2, stk) {
        (1, stk) => happyFail(1, tk, st, stses, stk),
        (j, HappyStk(v1, Some(box HappyStk(v2, Some(box HappyStk(v3, stk_q)))))) => {
            stses.remove(0);
            stses.remove(0);
            let sts = stses.clone();
            let st = stses.clone().remove(0);
            let HappyState(action) = st.clone();

            let r = __fn(v1, v2, v3);
            action(nt, j, tk, st, sts)(HappyStk(r, stk_q))
        },
        _ => {
            panic!("irrefutable pattern")
        }
    }
}

fn happyReduce<T: 'static>(k: isize, nt: isize,
                           __fn: Box<FnBox(Stack) -> Stack>,
                           _3: isize, tk: Token,
                           st: State<T>, sts: Vec<State<T>>, stk: Stack) -> Monad<T> {
    match _3 {
        1 => happyFail(1, tk, st, sts, stk),
        j => {
            let sts1 = happyDrop(k - 1, sts);
            let st1 = sts1.clone().remove(0);
            let HappyState(action) = st1.clone();
            let r = __fn(stk);
            action(nt, j, tk, st1, sts1)(r)
        },
    }
}

fn happyMonadReduce<T: 'static>(k: isize, nt: isize,
                                __fn: Box<FnBox(Stack, Token) -> Monad<HappyAbsSyn>>,
                                _3: isize, tk: Token,
                                st: State<T>, sts: Vec<State<T>>, stk: Stack) -> Monad<T> {
    match _3 {
        1 => happyFail(1, tk, st, sts, stk),
        j => {
            let sts1 = happyDrop(k, __op_concat(st, sts));
            let st1 = sts1.clone().remove(0);
            let HappyState(action) = st1.clone();

            let drop_stk = happyDropStk(k, stk.clone());

            happyThen1(__fn(stk.clone(), tk.clone()), box move |r| {
                action(nt, j, tk, st1, sts1)(HappyStk(r, Some(box drop_stk)))
            })
        }
    }
}

fn happyMonad2Reduce<T: 'static, U>(k: isize, nt: U,
                                    __fn: Box<FnBox(Stack, Token) -> Monad<HappyAbsSyn>>,
                                    _3: isize, tk: Token,
                                    st: State<T>, sts: Vec<State<T>>, stk: Stack) -> Monad<T> {
    match _3 {
        1 => happyFail(1, tk, st, sts, stk),
        j => {
            let sts1 = happyDrop(k, __op_concat(st, sts));
            let st1 = sts1.clone().remove(0);
            let HappyState(action) = st1.clone();

            let drop_stk = happyDropStk(k, stk.clone());

            let new_state = action;

            happyThen1(__fn(stk, tk), box move |r| {
                happyNewToken(curry_5_1!(new_state), sts1, HappyStk(r, Some(box drop_stk)))
            })
        }
    }
}

fn happyDrop<T>(n: isize, mut l: Vec<T>) -> Vec<T> {
    if n == 0 { l } else {
        l.remove(0);
        happyDrop(n - 1, l)
    }
}

fn happyDropStk<T>(n: isize, stk: HappyStk<T>) -> HappyStk<T> {
    match (n, stk) {
        (0, stk) => stk,
        (n, HappyStk(x, Some(box xs))) => happyDropStk(n - 1, xs),
        _ => panic!("irrefutable pattern"),
    }
}

// -----------------------------------------------------------------------------
// Moving to a new state after a reduction
fn happyGoto(action: Action<HappyAbsSyn, Stack>, j: isize, tk: Token,
             st: State<HappyAbsSyn>, sts: Vec<State<HappyAbsSyn>>, stk: Stack) -> Monad<HappyAbsSyn> {
    let action = Rc::new(action);
    let action_ = action.clone();
    action(j, j, tk, (HappyState(Rc::new(apply_5_1_clone!(action_)))), sts, stk)
}

// -----------------------------------------------------------------------------
// Error recovery (ERROR_TOK is the error token)
fn happyFail<T: 'static>(i: isize, tk: Token, old_st: State<T>, sts: Vec<State<T>>, stk: Stack) -> Monad<T> {
    match (i, old_st, stk) {
        (1, old_st, HappyStk(x, Some(_))) => {
            let i = match x {
                HappyErrorToken(i) => i,
                _ => unreachable!(),
            };
            happyError_(i, tk)
        },
        (i, HappyState(action), stk) => {
            action(1, 1, tk, HappyState(action.clone()), sts)(HappyStk(HappyErrorToken(i), Some(box stk)))
        },
    }
}

fn notHappyAtAll<a: 'static>() -> a {
    panic!("Internal Happy error")
}

// end of Happy Template.
